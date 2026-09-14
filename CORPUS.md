# The corpus

A CI service's build history.

Customers give you repositories. Every time someone pushes, you start a **run**.
A run fans out into **jobs**, one per machine — Linux, macOS, Windows — and each
job executes a handful of **steps**: checkout, build, test, lint, package,
deploy.

You bill for compute. A step that ran for `ms` milliseconds on a runner costing
`rate` per millisecond cost you `ms × rate`.

```
repo        a project someone is building
└── run     one build, triggered by a commit
    └── job one machine's share of that build
        └── step   one command inside that job
```

Four levels, three hops. Every level is an array: a repo has many runs, a run
has many jobs, a job has many steps.

---

## The JSON

One array of repos. Each carries its entire build history *inside it* — which
is what makes it a document and not a table.

```json
{
  "id": "9ac9d5ae-2851-4e0a-a319-340bc52ed89a",
  "name": "edge-api",
  "org": "stark",
  "private": true,
  "runs": [
    {
      "id": 2, "branch": "develop", "status": "timeout", "ms": 3045598, "trigger": "pr",
      "jobs": [
        {
          "id": 3, "os": "linux", "status": "ok", "ms": 430020, "exit": 26,
          "steps": [
            { "id": 4, "name": "test",    "ms": 11414, "rate": 0.00053,  "error": "\"edge-web\" not found" },
            { "id": 5, "name": "package", "ms": 28320, "rate": 0.000269, "error": null },
            { "id": 6, "name": "deploy",  "ms":  3674, "rate": 0.000483 }
          ]
        }
      ]
    }
  ]
}
```

About 900 bytes per repo. Nineteen fields in the whole schema.

### Three things a reader has to handle

**Optionality has two spellings.** Step 5 says `"error": null`. Step 6 leaves
`error` out entirely. They mean the same thing. So do `trigger` on a run and
`exit` on a job.

**Strings contain escapes.** `"\"edge-web\" not found"` — a reader that
mishandles them breaks here rather than passing by luck.

**A repo is identified by a uuid; everything below it by an integer.** A repo is
the thing customers name and link to, so its identity is stable and
unguessable. Runs, jobs and steps are only ever reached through their parent,
so a counter is enough — and those counters are unique across the whole corpus
rather than per table.

---

## The database

The same data, flattened. A nested array cannot be a column, so each becomes a
table, and each element remembers which parent it came from and where it sat in
the array.

```
   repo                run                  job                  step
   ┌──────────┐        ┌──────────┐         ┌──────────┐         ┌──────────┐
   │ id  uuid │◀───────│ repo_id  │◀────────│ run_id   │◀────────│ job_id   │
   │       PK │        │   uuid   │         │   int    │         │   int    │
   │ name     │        │ id    PK │         │ id    PK │         │ id    PK │
   │ org      │        │ idx      │         │ idx      │         │ idx      │
   │is_private│        │ branch   │         │ os       │         │ name     │
   └──────────┘        │ status   │         │ status   │         │ ms       │
                       │ ms       │         │ ms       │         │ rate     │
                       │ trigger ?│         │ exit    ?│         │ error   ?│
                       └──────────┘         └──────────┘         └──────────┘
```

`PK` primary key · `?` optional, the only columns that can be null

`idx` is the position the element held in its JSON array, kept because order is
information the array carried and a table would otherwise lose.

One field is renamed on the way in: the JSON key `private` is an OCaml keyword,
so the accessor is `is_private`.

A key is stored the way the thing it points at is stored. `repo.id` is a uuid,
so `run.repo_id` is a uuid too; `job.id` is an integer, so `step.job_id` is an
integer. The schema reader works that out for itself by following the
reference the `.mli` declares — `val repo_id : t -> Repo.id`.

### Types

| table | column | type | |
|---|---|---|---|
| `repo` | `id` | uuid | primary key |
| | `name` | string | |
| | `org` | string | one of five |
| | `is_private` | bool | JSON key `private` |
| `run` | `id` | int | primary key |
| | `repo_id` | uuid | → `repo.id` |
| | `idx` | int | position in `repo.runs` |
| | `branch` | string | main, develop, release |
| | `status` | string | ok, failed, cancelled, timeout |
| | `ms` | int | |
| | `trigger` | string? | push, pr, schedule |
| `job` | `id` | int | primary key |
| | `run_id` | int | → `run.id` |
| | `idx` | int | position in `run.jobs` |
| | `os` | string | linux, macos, windows |
| | `status` | string | |
| | `ms` | int | |
| | `exit` | int? | |
| `step` | `id` | int | primary key |
| | `job_id` | int | → `job.id` |
| | `idx` | int | position in `job.steps` |
| | `name` | string | checkout, build, test, lint, package, deploy |
| | `ms` | int | depends on which step it is — test is slowest |
| | `rate` | float | cost per millisecond |
| | `error` | string? | present on about one step in seven |

At 1.5 GB: 795,348 repos, 1,987,784 runs, 3,974,581 jobs, 13,911,204 steps.

---

## Running it

The whole back end, with no toolchain and no arguments:

```sh
docker run --rm -p 8000:8000 tatami/backend
```

That serves three tabs on <http://localhost:8000> — the data and what it
shreds into, the corpus queried by both stores side by side, and the
measurements charted. A 1,000-repo corpus is baked into the image so it works
offline; `-e TATAMI_ROWS=50000` or `-e TATAMI_BYTES=200M` generates a larger
one at startup from the same seed.

Postgres is not in that image. The tabs are served from the two in-memory
stores, and the database is only needed to check the shredding against SQL —
`docker compose up` brings both if you want that half.

## Getting it

`corpus/small.json` is checked in — 1,000 repos, 1.7 MB, enough to read and to
develop against. The full corpus is not, because it is deterministic from its
seed and regenerating is faster than copying:

```sh
dune exec bin/gen_corpus.exe -- --bytes 1.5G --seed 20260914 --out corpus/ci.json
dune exec bin/gen_corpus.exe -- --rows 5000  --seed 20260914 --out corpus/mid.json
```

**The file is one line.** No newline delimiters, so `head`, `wc -l` and
line-based streaming are no help, and `JSON.parse` on 1.5 GB will die — Node's
maximum string length is smaller than the file. Use a streaming reader
(`lib/corpus.ml` in OCaml, `ijson` in Python, `stream-json` in JS), or work
against `small.json`.

```sh
./db/up.sh                  # postgres
./db/load.sh                # shred the JSON into the four tables
dune exec bin/verify.exe    # assert the JSON and the database agree
```
