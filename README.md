# tatami

Derive a columnar schema from schemaless JSON, and measure what that buys.

## Run it

```sh
docker run --rm -p 8000:8000 durwasa/tatami-backend
```

<http://localhost:8000> — three tabs: the data and the four tables it shreds
into, the corpus queried by a row-major and a columnar store side by side, and
the measurements charted.

A 1,000-repo corpus is baked in, so that command needs no arguments and no
network. For a larger one, generated at startup from the same seed:

```sh
docker run --rm -p 8000:8000 -e TATAMI_ROWS=50000 durwasa/tatami-backend
docker run --rm -p 8000:8000 -e TATAMI_BYTES=200M durwasa/tatami-backend
```

## Build it

```sh
docker build -t durwasa/tatami-backend .
docker run --rm -p 8000:8000 durwasa/tatami-backend
```

## Publish it

One architecture, whatever machine you are on:

```sh
docker login
docker push durwasa/tatami-backend:latest
```

Both architectures, so it runs on Apple silicon and on x86 alike. Build it on
one machine, and `--push` sends the manifest and both images together:

```sh
docker login
docker buildx create --name tatami --use     # once
docker buildx build \
  --platform linux/amd64,linux/arm64 \
  -t durwasa/tatami-backend:latest \
  --push .
```

The amd64 half is emulated on an ARM machine, so it takes several minutes. An
image built with plain `docker build` carries only the architecture it was
built on, and fails with `exec format error` anywhere else.

## Without Docker

```sh
dune build
dune exec bin/serve.exe                      # localhost:8000
dune exec bin/gen_corpus.exe -- --bytes 1.5G --seed 20260914 --out corpus/ci.json
dune exec bin/bench.exe -- --corpus corpus/ci.json --json bench/results.jsonl
```

OCaml 5.2. The database half — shredding the same corpus into Postgres and
checking the two stores agree — is `docker compose up` then `./db/load.sh` and
`dune exec bin/verify.exe`.

## What it is

`CORPUS.md` describes the data and the schema. Briefly: a CI service's build
history, four levels deep, every level an array —

```
repo → run → job → step
```

Phase 1 infers the schema from document structure and emits one `.mli` per
table; those are in `schema/`. The columnar store allocates a dense typed array
per column, and a validity mask only where the `.mli` says a field is optional.
