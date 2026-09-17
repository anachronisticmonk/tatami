# tatami

Derive a columnar schema from schemaless JSON, and measure what that buys.

Phase 1 infers a schema from document structure and emits one `.mli` per table.
The columnar store then allocates a dense typed array per column, and a validity
mask only where the `.mli` says a field is optional — so what the types say is
what the memory layout is.

## Run it

```sh
docker run --rm -p 8000:8000 -p 8420:8420 durwasa/tatami
```

Two servers come up together:

- <http://localhost:8000> — the demonstration. Three tabs: one document beside
  the four tables it shreds into, the corpus queried by a row-major and a
  columnar store side by side, and the measurements charted.
- <http://localhost:8420> — the playground. Paste JSON, read the `.mli` it
  implies. `/translate` reaches the real Lean generator, not a reimplementation
  in the page.

A 1,000-repo corpus is baked in, so that command needs no arguments and no
network. For a larger one, generated at startup from the same seed — the same
corpus, longer:

```sh
docker run --rm -p 8000:8000 -p 8420:8420 -e TATAMI_ROWS=50000 durwasa/tatami
docker run --rm -p 8000:8000 -p 8420:8420 -e TATAMI_BYTES=200M durwasa/tatami
```

The image is `linux/amd64` and `linux/arm64`; Docker picks from the manifest.

## The corpus

A CI service's build history. Customers give you repositories; every push starts
a **run**, which fans out into **jobs**, one per machine, and each job executes
**steps** — checkout, build, test, lint, package, deploy. You bill for compute:
a step that ran `ms` milliseconds on a runner costing `rate` per millisecond
cost `ms × rate`.

```
repo        a project someone is building
└── run     one build, triggered by a commit
    └── job one machine's share of that build
        └── step   one command inside that job
```

Four levels, three hops, every level an array — which is what makes it a
document and not a table. A repo carries its entire build history inside it.

Three things a reader has to handle:

- **Optionality has two spellings.** A step may say `"error": null` or leave
  `error` out entirely. They mean the same thing. So do `trigger` on a run and
  `exit` on a job.
- **Strings contain escapes.** `"\"edge-web\" not found"` — a reader that
  mishandles them breaks here rather than passing by luck.
- **Ids are not uniform.** A repo is identified by a uuid; runs, jobs and steps
  by integers.

Shredded, each array becomes a table, and each element remembers which parent it
came from and where it sat in the array:

```
   repo                run                  job                  step
   ┌──────────┐        ┌──────────┐         ┌──────────┐         ┌──────────┐
   │ id    PK │◀───────│ repo_id  │◀────────│ run_id   │◀────────│ job_id   │
   │ name     │        │ id    PK │         │ id    PK │         │ id    PK │
   │ org      │        │ idx      │         │ idx      │         │ idx      │
   │is_private│        │ branch   │         │ os       │         │ name     │
   └──────────┘        │ status   │         │ status   │         │ ms       │
                       │ ms       │         │ ms       │         │ rate     │
                       │ trigger ?│         │ exit    ?│         │ error   ?│
                       └──────────┘         └──────────┘         └──────────┘
```

`PK` primary key · `?` optional — the only columns that can be null.

`idx` is the position the element held in its JSON array, kept because order is
information the array carried and a table would otherwise lose. One field is
renamed on the way in: the JSON key `private` is an OCaml keyword, so the
accessor is `is_private`.

`corpus/small.json` is checked in — 1,000 repos, 7.2 MB: 2,511 runs, 5,074 jobs,
17,744 steps. The full corpus is not, because it is deterministic from its seed
and regenerating is faster than copying:

```sh
dune exec bin/gen_corpus.exe -- --bytes 1.5G --seed 20260914 --out corpus/ci.json
dune exec bin/gen_corpus.exe -- --rows 5000  --seed 20260914 --out corpus/mid.json
```

At 1.5 GB that is 795,348 repos and 13,911,204 steps — large enough that
`JSON.parse` will die on it, since Node's maximum string length is smaller than
the file. Use a streaming reader (`lib/corpus.ml` in OCaml, `ijson` in Python,
`stream-json` in JS), or work against `small.json`.

## Build it

```sh
docker buildx build --builder multiarch \
  --platform linux/amd64,linux/arm64 \
  -t durwasa/tatami:latest \
  --push .
```

Three stages: the Lean generator, the OCaml servers, and a slim runtime that
carries only the two binaries and the pages. `--push` sends the manifest and
both images together. Plain `docker build` carries only the architecture it was
built on, and fails with `exec format error` anywhere else.

The amd64 half is emulated on an ARM machine. The build asserts the generator
answers before shipping it, in both architectures.

## Without Docker

OCaml 5.2 and the Lean toolchain in `lean-toolchain`.

```sh
lake build tatami                # the generator
dune build                       # the servers
dune exec bin/serve.exe          # localhost:8000
python3 dev/serve.py             # localhost:8420
dune exec bin/bench.exe -- --corpus corpus/small.json --json bench/results.jsonl
```

The database half — shredding the same corpus into Postgres and checking the two
stores agree — is the part the tabs do not show:

```sh
./db/up.sh                      # postgres on 5432, safe to run repeatedly
./db/load.sh                    # shred the JSON into the four tables
dune exec bin/verify.exe        # assert the JSON and the database agree
```

## Layout

```
Main.lean  Tatami.lean  Tatami/    the generator: inference and .mli emission
Proofs.lean  Proofs/               what is proved about it
lib/  bin/                         the OCaml stores, servers and benchmarks
schema/                            the .mli files phase 1 emits
web/  dev/serve.py                 the pages, and the playground server
examples/                          inputs worth reading whole, and their .mli
db/  schemacheck/  test/  bench/   postgres, schema checking, tests, timings
```
