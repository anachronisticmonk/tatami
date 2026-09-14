#!/bin/sh
# The image ships a 1,000-repo corpus so that `docker run` needs no arguments
# and no network. TATAMI_ROWS or TATAMI_BYTES regenerates a larger one before
# the server starts -- from the same seed, so it is the same corpus, longer.
set -e

CORPUS=${TATAMI_CORPUS:-corpus/small.json}
SEED=${TATAMI_SEED:-20260914}

if [ -n "$TATAMI_ROWS" ] || [ -n "$TATAMI_BYTES" ]; then
  CORPUS=corpus/generated.json
  if [ -n "$TATAMI_BYTES" ]; then
    echo "generating $TATAMI_BYTES corpus (seed $SEED)"
    tatami-gen --bytes "$TATAMI_BYTES" --seed "$SEED" --out "$CORPUS"
  else
    echo "generating $TATAMI_ROWS repos (seed $SEED)"
    tatami-gen --rows "$TATAMI_ROWS" --seed "$SEED" --out "$CORPUS"
  fi
fi

if [ "$1" = "tatami-serve" ]; then
  shift
  echo "tatami: serving $CORPUS on port ${TATAMI_PORT:-8000}"
  exec tatami-serve --corpus "$CORPUS" "$@"
fi

exec "$@"
