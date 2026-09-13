# Back end, second attempt

## Why we are starting again

The first attempt measured a kernel that had read the generated signature
against one that had not, and got 2.2x. It does not hold. Phase 1 turns JSON
into *tables*, so a `CREATE TABLE` must run before any query can, so the
catalog holds the column types and `attnotnull` holds the nullability. Two
catalog lookups and a binary result format bring a schema-blind kernel to the
same representation. The 2.2x measured a tooling default.

What survives is one axis: **layout**. Row-major against columnar, which no
amount of catalog reading changes. That is also a result from 2005 and not ours
to claim.

So the question this attempt asks is the one that is actually open:

> Given schemaless JSON, what does deriving a typed columnar schema buy,
> measured against what an OCaml programmer can do without one?

OCaml has no Arrow and no Parquet binding — `opam` has neither — so the
derivation is the only route to a columnar layout. Whether shredding earns back
what it costs is an open question with a number attached, and nobody has
measured it in a language with no columnar tooling.

## The corpus

CI build telemetry. Chosen because the nesting is natural rather than
contrived, and because every level is an array, which is the case the Lean
model handles with `coll` and which the first attempt never exercised.

```
repository                          A   the master
├── owner            object         →   ref: a table and an FK
├── topics           string[]       →   coll: scalar array, own table
└── runs             object[]       B   coll
    └── jobs         object[]       C   coll
        ├── labels   string[]       →   coll: scalar array
        └── steps    object[]       D   coll
```

`repository → runs → jobs → steps` is three hops, four levels. Seven tables
once shredded. Every level carries a nullable field so masks have something to
do, and int / float / bool / string all appear.

The query that has to separate the layouts:

```sql
select duration_ms * cost_per_ms from steps where duration_ms > 10
```

Two numeric columns, one predicate, one arithmetic result — the shape that was
never actually implemented last time.

---

## T1 · Corpus generator

- [x] ~~T1.1 Fix the domain: field names, types, which fields are nullable and
      at what rate, which are int vs float~~
- [x] ~~T1.2 `bin/gen_corpus.ml` — streams one JSON array to stdout/file, never
      holding the corpus in memory~~
- [x] ~~T1.3 Deterministic from a seed, so the corpus is reproducible and the
      Postgres load and the JSON reader see identical data~~
- [x] ~~T1.4 Size target 1.5 GB in a single `[{...},...]` file, with a `--rows`
      or `--bytes` flag so smaller corpora exist for the test suite~~
- [x] ~~T1.5 Sanity: valid JSON (round-trips through `yojson`), nesting depth is
      really four, nullable fields really are sometimes absent

## T2 · The .mli files (as if Phase 1 emitted them)~~
- [x] ~~T2.1 One `.mli` per table: `repository`, `owner`, `topic`, `run`, `job`,
      `label`, `step`~~
- [x] ~~T2.2 Foreign keys typed across modules — `val run_id : t -> Run.id` — so
      referential integrity is in the type system and not a convention~~
- [x] ~~T2.3 Array element tables carry `parent_id` and `idx`, per the Lean
      model's `coll`: the element points back, the parent holds no column~~
- [x] ~~T2.4 Extend `Schema.load` to read a qualified `Module.id` as a foreign
      key (a dense int). It currently understands only the unqualified types~~
- [x] ~~T2.5 Extend it again for multi-file schemas: a `Schema.t` today is one
      table, and this corpus is seven

## T3 · Postgres, faithfully~~
- [ ] T3.1 `db/schema.sql` — seven tables, FKs declared, column order matching
      the `.mli` order, `NOT NULL` exactly where the `.mli` says not-optional
- [ ] T3.2 Loader that reads the same generated corpus and shreds it into those
      tables, so the JSON and the database hold the *same* data and any
      difference in answers is a bug rather than a sampling artefact
- [ ] T3.3 `COPY` rather than `INSERT` — millions of rows
- [ ] T3.4 A check that round-trips: counts per table, a few spot rows, and one
      aggregate computed both from the JSON and from SQL and compared

## T4 · Path one — raw JSON, row-major

- [ ] T4.1 `lib/rowmajor/` — its own directory, its own dune library
- [ ] T4.2 Query the documents directly with `yojson`: parse per query, walk
      the nesting, no schema
- [ ] T4.3 Second variant: deserialise once into OCaml records, then query the
      record list. This is the honest strong baseline, not a straw man
- [ ] T4.4 Both must answer the workload correctly before anything is timed

## T5 · Path two — derived schema, typed columns

- [ ] T5.1 `lib/columnar/` — its own directory, its own dune library
- [ ] T5.2 Shred the corpus into one dense typed array per column, allocating a
      validity mask only where the `.mli` says `option`
- [ ] T5.3 Foreign keys as dense int columns; array tables carry `parent_id`
      and `idx` as ordinary columns
- [ ] T5.4 Query over the arrays: predicate, projection, and a computed column
      (`a * b`), which is where the layout should show
- [ ] T5.5 Joins across the four levels, since three hops is the point of the
      corpus and a single-table benchmark would dodge it

## T6 · Delete what does not survive

- [x] ~~T6.1 `lib/plain.ml`, `lib/tuned.ml`, `lib/run.ml` — written for the
      comparison we abandoned~~
- [~] T6.2 `lib/analysis.ml` deleted; `lib/dataflow.ml` — keep only if the new query
      path uses them; the constant/nullability lattice may survive, the
      filter/project plan probably does not
- [~] T6.3 deleted, not yet rewritten:  `bin/bench.ml`, `bin/serve.ml`, `web/*` — rewrite against the new
      shape rather than patch
- [x] ~~T6.4 `schema/orders.mli` and the old `orders` table

## T7 · Measure~~
- [ ] T7.1 The workload: point lookup by id, scan with predicate, computed
      column, aggregate, and a three-hop join
- [ ] T7.2 Report where row-major **wins** — point lookups and whole-document
      reads — because a result with a crossover is worth more than one without
- [ ] T7.3 Include the shredding cost. Columnar starts behind and has to earn
      it; the honest figure is the crossover, not the steady state
- [ ] T7.4 Variance: median of n, discard the first, and report the band rather
      than asserting it

## T8 · Hand the corpus to the front end

- [ ] T8.1 A single 1.5 GB `.json` file, plus the seed and the generator commit
      so it can be regenerated rather than copied
- [ ] T8.2 A short README next to it: the shape, the field types, which fields
      are nullable, and the seven tables it shreds into

---

## Open, not yet decided

- Whether the columnar store is built in memory only, or persisted. Residency
  across queries is a precondition for any amortisation, and the old server
  re-fetched per request, which put it permanently at k=0.
- Whether the constant/nullability lattice earns a place in this attempt. It
  proves `a * b` needs no mask, which is a real result, but it needs the query
  language to have expressions first.
