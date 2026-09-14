# What this data is

You run a CI service. Customers give you repositories; every time someone
pushes, you start a **run**. A run fans out into **jobs**, one per machine —
Linux, macOS, Windows — and each job executes a handful of **steps**:
checkout, build, test, lint, package, deploy.

You bill for compute. A step that ran for `ms` milliseconds on a runner costing
`rate` per millisecond cost you `ms × rate`. That product is the number the
business cares about, and it is the reason this corpus exists.

```
repo        a project someone is building
└── run     one build, triggered by a commit
    └── job one machine's share of that build
        └── step   one command inside that job
```

Four levels, three hops. Every level is an array, because a repo has many
runs, a run has many jobs, and a job has many steps.

---

# What the JSON is

One array of repos. Each one carries its entire build history *inside it* —
that is what makes it JSON and not a table.

```json
{
  "id": 1,
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

About 900 bytes per repo. Three things to notice:

**Optionality has two spellings.** Step 5 says `"error": null`. Step 6 leaves
`error` out entirely. They mean the same thing, and a reader has to treat them
the same. So do `trigger` on a run and `exit` on a job.

**Strings contain escapes.** `"\"edge-web\" not found"` — a reader that
mishandles them breaks on this corpus instead of passing by luck.

**Ids are unique across the whole corpus**, not per type. Repo 1, run 2, job 3,
step 4.

---

# What the database is

The same data, flattened. A nested array cannot be a column, so each becomes a
table, and each element remembers which parent it came from and where it sat in
the array.

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

`?` marks the four optional columns — the only four that get a validity mask.
`idx` is the position the element had in its JSON array, kept because order is
information the array carried and a table would otherwise lose.

One field gets renamed on the way in: the JSON key `private` is an OCaml
keyword, so the accessor is `is_private`. That renaming is what
`Proofs/Mangle.lean` proves injective — two distinct JSON keys can never
collide into one field name.

---

# What a query looks like

*"What did the slow steps cost us?"* — every step that ran longer than 30
seconds, and the total bill for them.

**In SQL**, once the data is shredded, it is one line:

```sql
select sum(ms * rate) from step where ms > 30000;
```

**In the JSON**, there is no `step` to select from. You have to go and find
them:

```ocaml
List.iter (fun repo ->
  List.iter (fun run ->
    List.iter (fun job ->
      List.iter (fun step ->
        if step.ms > 30000 then total := !total +. float_of_int step.ms *. step.rate)
        job.steps)
      run.jobs)
    repo.runs)
  corpus
```

Four nested loops to reach a value three levels down, and every repo, run and
job is walked whether or not it matters — because the only route to a step is
through the documents containing it.

**In the columnar store**, `ms` and `rate` are two flat arrays, and the answer
is one pass over both:

```ocaml
for i = 0 to n - 1 do
  let x = ms.(i) in
  if x > 30000 then acc := !acc +. float_of_int x *. rate.(i)
done
```

The other five columns of a step are not touched, not in the cache line, not
paged in. Neither array has a validity mask, because the `.mli` says `ms` and
`rate` are total — so there is no null check in that loop, and the product they
compute needs no mask of its own.

The same question, three shapes. Which one wins depends on the question, and
the whole point of the benchmark is that it is not always the last one:

| question | JSON is good at | columns are good at |
|---|---|---|
| everything about *this* repo | ✓ it is already one object | ✗ reassemble from 3 tables |
| how many steps over 30s | ✗ walk everything | ✓ one array |
| what the slow steps cost | ✗ walk everything | ✓ two arrays |
| build time for org `stark` | ✓ nesting is already there | ✗ three joins |

---

# Getting it

Deterministic from the seed, so regenerate rather than copy 1.5 GB around:

```sh
dune exec bin/gen_corpus.exe -- --bytes 1.5G --seed 20260914 --out corpus/ci.json
dune exec bin/gen_corpus.exe -- --rows 5000 --seed 20260914 --out corpus/small.json
```

`--rows N` for a fixed count, `--out -` for stdout. `corpus/` is git-ignored.

**The file is one line.** No newline delimiters, so `head`, `wc -l` and
line-based streaming are no help, and `JSON.parse` on 1.5 GB will die — Node's
maximum string length is smaller than the file. Use a streaming reader
(`lib/corpus.ml` in OCaml, `ijson` in Python, `stream-json` in JS), or develop
against `--rows 5000` and prove it against the full thing.

```sh
./db/up.sh                  # postgres
./db/load.sh                # shred the JSON into the four tables
dune exec bin/verify.exe    # assert the JSON and the database agree
dune exec bin/bench.exe     # the three stores, same questions
```

`verify` recomputes aggregates from both stores and compares them. If it
reports a difference, nothing measured against them means anything.
