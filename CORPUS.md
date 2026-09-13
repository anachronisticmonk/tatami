# The corpus

CI build telemetry, as one JSON array. Regenerate rather than copy — it is
deterministic from the seed, so everyone gets byte-identical files:

```sh
dune exec bin/gen_corpus.exe -- --bytes 1.5G --seed 20260914 --out corpus/ci.json
```

`159,388` repositories, `9,937,996` objects, 1.5 GB, about fifteen seconds.
`--rows N` gives a fixed count instead of a size; `--out -` writes to stdout.
`corpus/` is git-ignored for the obvious reason.

## Shape

```
repository                      the root
├── id              int
├── name            string
├── org             string
├── default_branch  string
├── is_private      bool
├── stars           int
├── created_at      int          epoch seconds
├── description     string?
├── owner           object       ──▶ one nested object
│   ├── id          int
│   ├── login       string
│   ├── kind        string       "user" | "org"
│   ├── followers   int
│   └── email       string?
├── topics          string[]     ──▶ array of scalars
└── runs            object[]     ──▶ array of objects
    ├── id          int
    ├── number      int
    ├── commit_sha  string       40 hex
    ├── branch      string
    ├── status      string       success | failure | cancelled | timed_out | skipped
    ├── started_at  int
    ├── duration_ms int
    ├── trigger     string?
    └── jobs        object[]
        ├── id          int
        ├── name        string
        ├── runner_os   string
        ├── status      string
        ├── duration_ms int
        ├── queued_ms   int
        ├── exit_code   int?
        ├── labels      string[]
        └── steps       object[]
            ├── id          int
            ├── name        string
            ├── status      string
            ├── duration_ms int
            ├── cost_per_ms float
            ├── log_bytes   int
            ├── memory_mb   int
            └── error       string?
```

`repository → runs → jobs → steps` is **three hops, four levels**.

## Things worth knowing before you parse it

**Optional fields appear in both of JSON's forms.** A field marked `?` above is
sometimes present, sometimes explicitly `null`, and sometimes **absent from the
object entirely** — roughly half and half between the last two. Treat absent and
null as the same thing; that is what the schema says and what the database does.

**Strings contain escapes.** `step.error` carries embedded double quotes, on
purpose:

```json
"error": "exit 78: \"edge-edge\" not found"
```

A reader that mishandles escapes fails on this corpus rather than passing by
luck.

**Ids are unique across the whole corpus**, not per type — the generator hands
out one sequence to repositories, owners, runs, jobs and steps alike. Elements
of the two scalar arrays (`topics`, `labels`) have no id in the JSON; one is
synthesised when they are shredded.

**The array is one line.** No newline delimiters, so line-based tooling will
not help. `lib/corpus.ml` streams the top-level elements without building a
tree if you need that in OCaml.

## Shredded

Seven tables, one per `.mli` in `schema/`:

| table | from | key back to parent |
|---|---|---|
| `repository` | the root | — |
| `owner` | `repository.owner` | parent holds `owner_id` |
| `topic` | `repository.topics[]` | `repository_id`, `idx` |
| `run` | `repository.runs[]` | `repository_id`, `idx` |
| `job` | `…runs[].jobs[]` | `run_id`, `idx` |
| `label` | `…jobs[].labels[]` | `job_id`, `idx` |
| `step` | `…jobs[].steps[]` | `job_id`, `idx` |

A nested **object** becomes a table the parent points *into*. An **array**
becomes a table whose elements point *back*, carrying `idx` so the order they
had in the JSON survives.

```sh
./db/up.sh          # postgres container
./db/load.sh        # shred corpus/ci.json into the seven tables
dune exec bin/verify.exe   # assert the JSON and the database agree
```

`verify` recomputes fifteen aggregates from both stores and compares them —
counts at every level, sums of columns at every level, and the float product
`duration_ms * cost_per_ms`. If it reports a difference, nothing measured
against these two stores means anything.
