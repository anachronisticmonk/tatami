#!/bin/sh
# One container, two servers: the demonstration on TATAMI_PORT (8000) and the
# playground on TATAMI_PLAYGROUND_PORT (8420).
#
#   docker run --rm -p 8000:8000 -p 8420:8420 durwasa/tatami
#
# Plain sh rather than supervisord or s6, for three reasons that all point the
# same way. First, what a process supervisor is for is keeping a service up --
# restarting it, backing off, ordering dependencies -- and that is the opposite
# of what is wanted here: if either server dies the container should die, so
# that whatever is watching the container (compose, a scheduler, a human
# reading `docker ps`) sees a failure instead of a container that is up and
# half-working. Second, both are a dependency: an apt or apk layer, a config
# file in its own syntax, and a second thing to know before you can read the
# startup path. Third, sh is already PID 1 here, and PID 1's real job -- signal
# forwarding and reaping -- is twenty lines, written below.
#
# The contract: both start, either one's exit takes the container with it, and
# SIGTERM reaches both children so `docker stop` is a second rather than the
# ten it waits before SIGKILL.

set -eu

# bin/serve.exe reads "schema" and "corpus/..." relative to the working
# directory, so there is one.
: "${TATAMI_ROOT:=/app}"
cd "$TATAMI_ROOT"

# 0.0.0.0 for both, and not as a default buried in the programs: a published
# port forwards to the container's external interface, so a server on 127.0.0.1
# is reachable only from inside the container -- indistinguishable, from
# outside, from a broken port mapping.
: "${TATAMI_ADDR:=0.0.0.0}"
: "${TATAMI_PORT:=8000}"
: "${TATAMI_PLAYGROUND_ADDR:=0.0.0.0}"
: "${TATAMI_PLAYGROUND_PORT:=8420}"
: "${TATAMI_WEB:=$TATAMI_ROOT/web}"
: "${TATAMI_BINARY:=$TATAMI_ROOT/.lake/build/bin/tatami}"
: "${TATAMI_CORPUS:=corpus/small.json}"
: "${TATAMI_SERVE:=$TATAMI_ROOT/bin/serve.exe}"
: "${TATAMI_PLAYGROUND_SERVE:=$TATAMI_ROOT/dev/serve.py}"
: "${PYTHON:=python3}"
export TATAMI_ADDR TATAMI_PORT TATAMI_PLAYGROUND_ADDR TATAMI_PLAYGROUND_PORT \
       TATAMI_WEB TATAMI_BINARY

backend_pid=''
playground_pid=''
stopping=''

log() { echo "entrypoint: $*"; }

# Forward the signal on, once. Two signals arriving (docker stop then an
# impatient second one) must not turn into two rounds of killing.
stop() {
    # `if` rather than `[ ... ] && return`: under `set -e` an and-list that
    # ends false is a failed command, and the shell would exit here instead of
    # returning to the loop.
    if [ -n "$stopping" ]; then return 0; fi
    stopping=1
    log "stopping; forwarding SIGTERM to $backend_pid and $playground_pid"
    kill -TERM "$backend_pid" "$playground_pid" 2>/dev/null || true
}

trap 'stop' TERM INT HUP

# The image ships a 1,000-repo corpus so that `docker run` needs no arguments
# and no network. TATAMI_ROWS or TATAMI_BYTES regenerates a larger one before
# either server starts -- from the same seed, so it is the same corpus, longer.
: "${TATAMI_GEN:=$TATAMI_ROOT/bin/gen_corpus.exe}"
: "${TATAMI_SEED:=20260914}"

if [ -n "${TATAMI_ROWS:-}" ] || [ -n "${TATAMI_BYTES:-}" ]; then
    TATAMI_CORPUS=corpus/generated.json
    if [ -n "${TATAMI_BYTES:-}" ]; then
        log "generating a $TATAMI_BYTES corpus (seed $TATAMI_SEED)"
        "$TATAMI_GEN" --bytes "$TATAMI_BYTES" --seed "$TATAMI_SEED" --out "$TATAMI_CORPUS"
    else
        log "generating $TATAMI_ROWS repos (seed $TATAMI_SEED)"
        "$TATAMI_GEN" --rows "$TATAMI_ROWS" --seed "$TATAMI_SEED" --out "$TATAMI_CORPUS"
    fi
fi

log "root         $TATAMI_ROOT"
log "backend      $TATAMI_SERVE          -> http://$TATAMI_ADDR:$TATAMI_PORT (corpus $TATAMI_CORPUS)"
log "playground   $TATAMI_PLAYGROUND_SERVE -> http://$TATAMI_PLAYGROUND_ADDR:$TATAMI_PLAYGROUND_PORT (generator $TATAMI_BINARY)"

# Started directly, not through a wrapper subshell: $! has to be the server
# itself, or the TERM above would land on a shell and leave the server running
# until SIGKILL.
"$TATAMI_SERVE" --corpus "$TATAMI_CORPUS" &
backend_pid=$!

"$PYTHON" -u "$TATAMI_PLAYGROUND_SERVE" &
playground_pid=$!

log "backend pid $backend_pid, playground pid $playground_pid"

# Why poll instead of `wait -n`: `wait -n` (return when ANY child exits) is
# bash 4.3 and later, and /bin/sh is dash on Debian and ash on Alpine, where it
# is missing or recent. A one-second poll is portable and, for noticing that a
# server has died, one second is not a latency anybody can feel.
#
# The sleep runs in the background and is waited on rather than run in the
# foreground, because a trap handler runs only when the shell is between
# commands or in `wait`: a foreground `sleep 1` would swallow SIGTERM for up to
# a second. `wait` also reaps -- which matters twice over, because PID 1 is
# where orphans come to be reaped, and because `kill -0` succeeds on a zombie,
# so an unreaped child would look alive forever.
while :; do
    kill -0 "$backend_pid" 2>/dev/null || break
    kill -0 "$playground_pid" 2>/dev/null || break
    if [ -n "$stopping" ]; then break; fi
    sleep 1 &
    wait "$!" 2>/dev/null || true
done

status=0
if [ -z "$stopping" ]; then
    # Nobody asked for this: one of the two fell over. Take the other with it,
    # and exit nonzero so the container is visibly failed and not merely gone.
    if kill -0 "$backend_pid" 2>/dev/null; then
        log "the playground exited on its own; stopping the backend"
    else
        log "the backend exited on its own; stopping the playground"
    fi
    status=1
    stopping=1
    kill -TERM "$backend_pid" "$playground_pid" 2>/dev/null || true
fi

# Give them a moment to go down cleanly, then insist. Ten seconds is under
# `docker stop`'s own patience, so the SIGKILL that happens is ours, aimed at
# one process, rather than the runtime's, aimed at the container.
i=0
while [ "$i" -lt 10 ]; do
    kill -0 "$backend_pid" 2>/dev/null || kill -0 "$playground_pid" 2>/dev/null || break
    sleep 1 &
    wait "$!" 2>/dev/null || true
    i=$((i + 1))
done
kill -KILL "$backend_pid" "$playground_pid" 2>/dev/null || true
wait 2>/dev/null || true

log "both stopped; exiting $status"
exit "$status"
