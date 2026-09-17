# tatami, whole, in one container.
#
#   docker buildx build --builder tatami -t durwasa/tatami --load .
#   docker run --rm -p 8000:8000 -p 8420:8420 durwasa/tatami
#
# Two servers come up together:
#   :8000  the demonstration -- one document beside the tables it shreds into,
#          the corpus queried by a row-major and a columnar store, the charts
#   :8420  the playground -- paste JSON, read the .mli it implies
#
# Postgres is deliberately not in here. The three tabs are served from the two
# in-memory stores -- that is the whole demonstration -- and the database is
# only needed by bin/verify.exe, which checks the shredding against SQL.

# ---- the generator ----------------------------------------------------------
# debian:12-slim rather than a Lean image, so the binary's glibc is the glibc of
# the runtime it is copied into. lake-manifest.json lists no packages, so this
# is a self-contained build; the community Lean images carry mathlib's
# dependencies, which this does not have.
FROM debian:12-slim AS lean

RUN apt-get update \
 && apt-get install -y --no-install-recommends curl ca-certificates git build-essential \
 && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/opt/elan \
    PATH=/opt/elan/bin:$PATH
WORKDIR /src

# Keyed on lean-toolchain alone, so editing a .lean file below does not
# re-fetch the toolchain.
COPY lean-toolchain ./lean-toolchain
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      -o /tmp/elan-init.sh \
 && sh /tmp/elan-init.sh -y --default-toolchain "$(cat lean-toolchain)" \
 && rm /tmp/elan-init.sh

COPY lakefile.toml lake-manifest.json ./
COPY Main.lean Tatami.lean Proofs.lean ./
COPY Tatami/ ./Tatami/
COPY Proofs/ ./Proofs/
RUN lake build tatami

# Fail the build rather than ship a generator that does not answer.
RUN echo '[{"id":"a","n":1}]' | /src/.lake/build/bin/tatami --json | grep -q '"ok":true'

# ---- the servers ------------------------------------------------------------
FROM ocaml/opam:debian-12-ocaml-5.2 AS build

WORKDIR /src
RUN sudo apt-get update \
 && sudo apt-get install -y --no-install-recommends pkg-config libgmp-dev \
 && sudo rm -rf /var/lib/apt/lists/*

# Dependencies first, so editing source does not reinstall the world.
RUN opam install -y dune yojson tiny_httpd pgx pgx_unix bisect_ppx alcotest

COPY --chown=opam:opam dune-project dune ./
COPY --chown=opam:opam lib lib
COPY --chown=opam:opam bin bin
COPY --chown=opam:opam schema schema
RUN eval $(opam env) && dune build --profile release bin/serve.exe bin/gen_corpus.exe

# ---- what runs --------------------------------------------------------------
FROM debian:12-slim

# python3 for the playground server. debian:12-slim has none. Not
# python3-minimal: its stdlib is stripped of exactly what dev/serve.py imports
# -- http.server, json, pathlib, subprocess, tempfile -- and of the
# urllib.request the HEALTHCHECK below uses. The image built and pushed fine
# with it; the playground then died on `No module named 'http'` and the
# entrypoint correctly took the backend down with it.
RUN apt-get update \
 && apt-get install -y --no-install-recommends python3 \
 && rm -rf /var/lib/apt/lists/* \
 && useradd --create-home --shell /usr/sbin/nologin tatami

WORKDIR /app

COPY --from=build /src/_build/default/bin/serve.exe      bin/serve.exe
COPY --from=build /src/_build/default/bin/gen_corpus.exe bin/gen_corpus.exe
COPY --from=lean  /src/.lake/build/bin/tatami            .lake/build/bin/tatami

COPY schema  schema
COPY web     web
COPY bench   bench
COPY dev     dev
COPY corpus/small.json corpus/small.json
COPY docker-entrypoint.sh /usr/local/bin/

RUN chown -R tatami:tatami /app && chmod +x /usr/local/bin/docker-entrypoint.sh
USER tatami

# A bigger corpus than the one baked in, generated at startup from the same
# seed:  docker run -p 8000:8000 -p 8420:8420 -e TATAMI_ROWS=50000 durwasa/tatami
ENV TATAMI_ROOT=/app \
    TATAMI_PAGE=index.html \
    TATAMI_PORT=8000 \
    TATAMI_PLAYGROUND_PORT=8420
EXPOSE 8000 8420

# Both ports, because one alone would call the container healthy while the
# other half is down.
HEALTHCHECK --interval=30s --timeout=4s --start-period=40s --retries=3 \
  CMD python3 -c "import urllib.request as u,sys;[u.urlopen(f'http://127.0.0.1:{p}/',timeout=3) for p in (8000,8420)]" || exit 1

# Exec form: the script must be PID 1 to receive the signals it forwards.
ENTRYPOINT ["/usr/local/bin/docker-entrypoint.sh"]
