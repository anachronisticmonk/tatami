# tatami's back end, in one container.
#
#   docker build -t tatami/backend .
#   docker run --rm -p 8000:8000 tatami/backend
#
# Postgres is deliberately not in here. The three tabs are served from the two
# in-memory stores -- that is the whole demonstration -- and the database is
# only needed by bin/verify.exe, which checks the shredding against SQL. Adding
# it would double the image to prove something the container is not showing.

# ---- build ------------------------------------------------------------------
FROM ocaml/opam:debian-12-ocaml-5.2 AS build

WORKDIR /src
RUN sudo apt-get update \
 && sudo apt-get install -y --no-install-recommends pkg-config libgmp-dev \
 && sudo rm -rf /var/lib/apt/lists/*

# Dependencies first, so editing source does not reinstall the world.
RUN opam install -y dune yojson tiny_httpd pgx pgx_unix bisect_ppx alcotest

COPY --chown=opam:opam dune-project ./
COPY --chown=opam:opam lib lib
COPY --chown=opam:opam bin bin
COPY --chown=opam:opam schema schema
RUN eval $(opam env) && dune build --profile release bin/serve.exe bin/gen_corpus.exe

# ---- run --------------------------------------------------------------------
FROM debian:12-slim

RUN useradd --create-home --shell /usr/sbin/nologin tatami
WORKDIR /app

COPY --from=build /src/_build/default/bin/serve.exe      /usr/local/bin/tatami-serve
COPY --from=build /src/_build/default/bin/gen_corpus.exe /usr/local/bin/tatami-gen

COPY schema  schema
COPY web     web
COPY bench   bench
COPY corpus/small.json corpus/small.json
COPY docker-entrypoint.sh /usr/local/bin/

RUN chown -R tatami:tatami /app && chmod +x /usr/local/bin/docker-entrypoint.sh
USER tatami

# A bigger corpus than the one baked in, generated at startup:
#   docker run -p 8000:8000 -e TATAMI_ROWS=50000 tatami/backend
# Which page `/` serves. A second container with TATAMI_PAGE=reassemble.html
# gives that page a port of its own, with the API it calls on the same origin.
ENV TATAMI_PAGE=index.html
ENV TATAMI_PORT=8000
# Published ports forward to the container's external interface, so the server
# must not bind loopback here or it is reachable only from inside.
ENV TATAMI_ADDR=0.0.0.0
EXPOSE 8000

ENTRYPOINT ["docker-entrypoint.sh"]
CMD ["tatami-serve"]
