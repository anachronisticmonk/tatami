# Tatami — a proved derivation from schemaless JSON to typed columns

*A functional-programming hackathon project. Lean 4 infers a schema and proves
the inference correct; OCaml streams the data into typed columnar tables and
measures what the typing bought.*

---

## Contents

1. [The problem](#1-the-problem)
2. [The thesis: an `.mli` is a contract](#2-the-thesis-an-mli-is-a-contract)
3. [Inference in Lean 4](#3-inference-in-lean-4)
4. [What is proved](#4-what-is-proved)
5. [The emitted contract](#5-the-emitted-contract)
6. [The OCaml pipeline](#6-the-ocaml-pipeline)
7. [The columnar store: layout derived from types](#7-the-columnar-store-layout-derived-from-types)
8. [Method: correctness before speed](#8-method-correctness-before-speed)
9. [Results](#9-results)
10. [Selectivity](#10-selectivity)
11. [The gap in the OCaml ecosystem](#11-the-gap-in-the-ocaml-ecosystem)
12. [Limitations](#12-limitations)
13. [Reproducing everything](#13-reproducing-everything)

---

## 1. The problem

The corpus is a CI service's build history. A customer has repositories; every
push starts a **run**; a run fans out into **jobs**, one per machine; each job
executes **steps** — checkout, build, test, lint, package, deploy. Billing is by
compute: a step that ran `ms` milliseconds on a runner costing `rate` per
millisecond cost `ms × rate`.

```
repo        a project someone is building
└── run     one build, triggered by a commit
    └── job one machine's share of that build
        └── step   one command inside that job
```

Four levels, three hops, every level an array. A repository carries its entire
build history *inside* it, which is what makes the data a document rather than a
table. Nothing declares the shape.

Three properties make this harder than a toy:

**Optionality has two spellings.** A step may carry `"error": null`, or omit
`error` entirely. They mean the same thing, and any inference that treats them
differently is wrong.

**Strings contain escapes.** `"\"edge-web\" not found"` — a reader that
mishandles them breaks here rather than passing by luck.

**Ids are not uniform.** A repository is identified by a uuid; runs, jobs and
steps by integers.

The ordinary response is to guess the schema, hand-write a loader, and discover
the guess was wrong in production. The failure is asymmetric: a schema that says
`string` where the data needs `string option` produces OCaml that **compiles
cleanly**, passes whatever tests the sample data supports, and then fails at
load on the first document that omits the field. A careful loader reports that
well — ours names the column — but it is still a run-time discovery about a
program that type-checked.

So the real question is not *can we infer a schema*. It is **can we infer one we
are entitled to rely on.**

---

## 2. The thesis: an `.mli` is a contract

An OCaml signature file sits on a boundary and states exactly what crosses it.
That is precisely the job an inferred schema needs to do, so that is where we
put it — not in a JSON-schema document that some loader re-interprets at
runtime, but in a file the OCaml compiler enforces at every call site.

Two consequences follow, and they are the heart of the project.

**First, the schema stops being advisory.** If inference says `ms : int`, then
every piece of code that touches `ms` is type-checked against that claim. There
is no runtime validation step to forget, and no drift between the documented
schema and the code that reads it.

**Second — and this is why the proof matters — because the signature is
*generated*, we can prove things about the generator.** A hand-written contract
can only be trusted as far as its author. A generated one can carry a theorem.

---

## 3. Inference in Lean 4

Inference walks the documents and, for every member of every table, accumulates
an observation record. Two things are computed.

**The principal type.** For each member, the least type in the lattice that
admits every value observed there. "Least" is doing real work: adequacy alone is
nearly free — a corpus of integers is adequately described by `float`, and also
by `int option`. Minimality is what rules those loose answers out. The two
together pin the type from both sides, which is what *principal* means.

**The counts.** For each member of each table: how many times a value was
present (`values`), how many times it was explicitly `null` (`nulls`), and how
many times it was absent (`absent`), against how many times the table was
visited at all (`visits`).

A member is optional exactly when it carried a value fewer times than its table
was visited. Note the shape of this: absence is not observed directly, it is
*computed* — and computed by truncating subtraction, which is exactly where a
soundness bug would hide. Chapter 4 is largely about closing that hole.

---

## 4. What is proved

**221 theorems and lemmas across twelve files, zero `sorry`s.** They compose
into a single top-level result, `pipeline_correct`, stated in five named parts
so the guarantee can be read without opening nine files.

### 4.1 Well-formedness

> The emitted signature repeats no module name, no value name within a module,
> and no field name within a record.

This is what "the output is legal OCaml" amounts to for this fragment. It holds
of every schema because the generator checks its own output.

### 4.2 Canonicity

> ```lean
> theorem schema_canonical (cfg : Config) (ds : List Doc) (ts : Tables)
>     (hinf : inferCorpus cfg ds = .ok ts) :
>     ∀ es ts', ds.Perm es → inferCorpus cfg es = .ok ts' → ts = ts'
> ```

The schema is determined by the corpus **as a collection of documents**, not by
the order they arrived in. Shuffle the corpus and the answer is *equal*, not
merely equivalent. That distinction is what makes two runs of the generator
agree byte for byte — which in turn is what makes the generated code
reproducible and diffable in version control.

### 4.3 Structure preservation

> The tree the documents induce and the graph a reader finds in the generated
> signatures are the **same graph**.

Six clauses, each load-bearing. The first two say no edge is lost; the next two
that none is invented — together the edge sets agree. The fifth says distinct
tables get distinct modules, which lifts "the same edges" to "the same graph"
rather than a collapse of one onto a smaller one. The sixth says the graph is
rooted, so walking from the root module reaches everything — without it a table
could be declared and never reachable, which is a table the loader would create
and never fill.

### 4.4 Principality

> Each member is given the principal type of the values seen there: one that
> admits every one of them (*adequacy*), and the least type that does
> (*minimality*).

### 4.5 Nullability — the sharpest part

> ```lean
> theorem nullability_sound … :
>   o.values + o.nulls + o.absent = t.visits
>   ∧ (o.nullable = true ↔ o.values < t.visits)
> ```

Two halves. The **counts identity** says every visit to a table is accounted for
at each of its members — a value, an explicit `null`, or an absence, and nothing
else. The second half reads the flag off that identity: `nullable` is set
precisely when the member carried a value in fewer than all of its table's
visits.

Why the identity is necessary: absence is computed by *truncating* subtraction.
Without it, a member some document had omitted could report `absent = 0`, come
out non-optional, and the generator would emit `string` where the data needs
`string option`.

The columnar builder does defend itself — a total column that meets a `null`
raises `<column> is NULL in the data, but its signature says otherwise` rather
than storing an initialiser and calling it a value. So the consequence is a
loud abort, not corruption. But it is an abort at load time, on production
data, in code a theorem prover generated and the compiler accepted. The
theorem does not make the crash survivable; it makes the condition
unreachable.

Together with principality, this is the whole of what a generated field
declaration claims: principality pins the type from both sides, nullability pins
the `option` from both sides.

### 4.6 What the proof does *not* say

Stated explicitly in the source, and worth repeating because an overclaimed
guarantee is worse than a modest one:

- **Nothing about refused input.** Every conjunct is conditional on
  `inferCorpus` and `gen` both returning `ok`. Both refuse inputs — a member
  holding two types with no common type, a schema whose tree a signature cannot
  express. The guarantee is about what is *emitted*, not about what is accepted.
- **Nothing about rows.** The program emits a description of tables; the loader
  that fills them is OCaml, outside what Lean sees. A preservation theorem for
  rows would need the shredder formalised first.

---

## 5. The emitted contract

Lean emits one `.mli` per table, the corresponding `.ml`, and a loader.

```ocaml
(* step.mli — generated *)
type t
type id = int
val make : id:int -> job_id:Job.id -> idx:int ->
           error:string option -> ms:int -> name:string -> rate:float -> t
val get    : id -> t
val of_job : Job.id -> t list
val id     : t -> int
val job_id : t -> Job.id
val idx    : t -> int
val error  : t -> string option
val ms     : t -> int
val name   : t -> string
val rate   : t -> float
```

Read that and you know the table: its columns, their types, that `error` is the
only column that can be null, and how it links to its parent. Several details
are deliberate:

- **`of_job : Job.id -> t list`** — the foreign key, expressed as a function.
  The relationship is part of the contract, not a convention in a comment.
- **`idx : t -> int`** — the position the element held in its JSON array, kept
  because order is information the array carried and a table would otherwise
  lose.
- **`ms : t -> int`, not `int option`** — the data never lacked it, and the
  theorem in 4.5 is why that claim is safe to build on.
- **`Repo.id = uuid = string`**, while `Run.id`, `Job.id` and `Step.id` are all
  `= int`. So the compiler genuinely separates a repository id from the others,
  but it does **not** stop you passing a run id where a job id is expected —
  these are manifest type abbreviations, not abstract types. Making them
  abstract is the obvious next increment; see chapter 12.
- One field is renamed on the way in: the JSON key `private` is an OCaml
  keyword, so the accessor is `private_`.

---

## 6. The OCaml pipeline

A streaming loader shreds documents into four tables — `repo`, `run`, `job`,
`step` — preserving referential integrity: every child row records the parent it
came from and the position it held in its array.

The corpus is read as a stream rather than parsed whole. At 1.5 GB the file is
larger than Node's maximum string length, so `JSON.parse` dies on it outright;
`lib/corpus.ml` reads it incrementally.

The same loader populates Postgres through **`pgx`** (`bin/load.ml`,
`schema/loader.ml`, `lib/shred/`), which gives the whole shredding an
independent check: `bin/verify.exe` asserts that the JSON and the relational
store hold the same data. That half is not visible in the browser
demonstration — the three tabs are served from the two in-memory stores — but it
is what makes "referential integrity is preserved" a checked claim rather than
an assertion.

---

## 7. The columnar store: layout derived from types

One dense typed array per column. From the source:

> What each column *is* comes from the `.mli` and from nowhere else. The array
> type is chosen by the layout the schema reader parsed, and a validity mask is
> allocated only where that layout says `option` — so a column the signature
> calls total has **no mask, no branch, and no memory holding either**. Nothing
> here special-cases a column by name.

This is the payoff, and it is the reason chapter 4.5 had to be a theorem. The
error is asymmetric in both directions:

| Error | Cost |
|---|---|
| `option` where the data is total | a mask, a branch, and the memory to hold them — on every row, forever |
| total where the data is optional | a crash on the first absent value |

Exactness is therefore not a nicety; it is the precondition for the layout being
sound at all.

**One implementation note worth recording**, because it is where most of the
performance went. Columns are grown in fixed chunks rather than by doubling. The
row count is not known until the corpus has been read, and counting first would
mean parsing 1.5 GB twice. Doubling was the first attempt and scaled badly:
every doubling copies the whole array and a final trim copies it again, so
filling *n* elements moves about *3n* through the major heap. At thirteen
million elements that showed up as a **2.6× penalty** against the row-major
store. Chunking moves exactly *n*, with peak memory *2n* at the final blit
rather than *3n* during a doubling.

---

## 8. Method: correctness before speed

Three stores are compared:

| Store | What it is |
|---|---|
| `json` | raw Yojson — traverse the document tree directly |
| `records` | row-major: a record list, the ppx-deriving-json shape |
| `columnar` | the derived-schema store of chapter 7 |

All three implement the **same** signature. From `lib/workload.ml`:

> Both paths implement this signature, which is the point of having one: a
> benchmark where each side answers a question shaped to suit it measures
> nothing. The answers are compared before the timings are believed.

The five queries were chosen to have a crossover in them rather than to flatter
columns:

| Query | What it does |
|---|---|
| `document` | everything under one repository — the case a row store exists for, which row-major holds contiguously and the columnar side must reassemble by scanning three tables |
| `scan` | how many steps ran longer than *n* — one column out of ten |
| `computed` | `sum(ms × rate)` over steps longer than *n* — two columns, arithmetic, a computed result |
| `by_status` | the longest step under each status — five groups over the whole table |
| `three_hop` | total step duration for one organisation: step → job → run → repo |

`bin/bench.ml` counts disagreements and, if any exist, prints *"N disagreements
— timings below are meaningless"*. **There are none, on every corpus.** Float
sums are compared to a relative tolerance because they are accumulated in a
different order on each side; everything else is integral and must match
exactly.

Only then are the timings worth reading.

---

## 9. Results

Columnar speedup over the row-major record store, five repeats per point.
Values above 1.0 mean columnar is faster.

| Corpus | `document` | `scan` | `computed` | `by_status` | `three_hop` |
|---|---|---|---|---|---|
| 10 MB | 0.47× | 2.95× | 4.25× | 1.24× | 0.38× |
| 25 MB | 0.51× | 2.93× | 3.22× | 1.24× | 0.45× |
| 50 MB | 0.72× | 3.21× | 3.34× | 1.26× | 0.64× |
| 100 MB | 0.81× | 3.23× | 3.47× | 1.28× | 0.90× |
| 200 MB | 0.46× | 3.33× | 3.49× | 1.28× | 1.20× |

Against raw Yojson document traversal, both typed stores are roughly **50×–540×**
faster on scans, and effectively unbounded on keyed lookup (a hash lookup versus
a full document walk).

### Load time and memory

| Corpus | records load | records mem | columnar load | columnar mem |
|---|---|---|---|---|
| 10 MB | 398 ms | 15.1 MB | 279 ms | 13.5 MB |
| 50 MB | 969 ms | 74.9 MB | 1311 ms | 66.7 MB |
| 200 MB | 4014 ms | 296.9 MB | 5229 ms | 264.2 MB |

Two honest observations. **Columnar memory is consistently smaller** — 264 MB
against 297 MB at 200 MB of input — and that difference is largely the masks
that total columns do not allocate. But **columnar load is slower at scale**:
shredding is real work, and at 200 MB it costs about 30% more wall-clock to
build. The trade is paid once at load and recovered on every scan.

### What we are not claiming

**We are not claiming to have built a faster database.** Two of the five queries
go the other way, by design — `document` is the case a row store exists for, and
if columns won that one too the benchmark would be wrong somewhere.

The claim is narrower and more useful: **once the type is known, the queries
that touch few columns over many rows get substantially faster, and you can
predict which ones from the schema alone, before reading a row.**

---

## 10. Selectivity

Sweeping the predicate threshold of `scan` across the 50 MB corpus:

| Threshold | Rows kept | % | row-major | columnar | Speedup |
|---|---|---|---|---|---|
| 899 000 | 71 | 0.02% | 3.925 ms | 0.279 ms | **14.07×** |
| 700 000 | 17 632 | 3.78% | 3.702 ms | 0.411 ms | 9.01× |
| 400 000 | 43 817 | 9.39% | 3.950 ms | 0.564 ms | 7.00× |
| 200 000 | 88 831 | 19.05% | 4.089 ms | 0.829 ms | 4.93× |
| 100 000 | 138 219 | 29.64% | 4.444 ms | 1.123 ms | 3.96× |
| 30 000 | 251 920 | 54.01% | 5.374 ms | 1.602 ms | 3.35× |
| 5 000 | 375 976 | 80.61% | 4.133 ms | 0.774 ms | 5.34× |
| 1 000 | 457 626 | 98.12% | 3.862 ms | 0.289 ms | 13.36× |
| 0 | 466 402 | 100.00% | 3.777 ms | 0.247 ms | **15.29×** |

A **U-curve**. Highly selective predicates and full scans both do very well; the
middle, around half the rows surviving, is where per-row branching costs most.

This is exactly the shape a query planner wants to know about — and the schema
already says which columns are scannable and which are nullable before a single
row is read. A planner over these types could reasonably decide: *this predicate
is on a total `int` column, expected selectivity is extreme, choose the columnar
path.* That is the concrete form of "the types enable optimisation" — not a
slogan, a decision procedure with a measured curve behind it.

---

## 11. The gap in the OCaml ecosystem

**The columnar options in OCaml are all foreign.** Two exist, and it is worth
naming them rather than claiming a void:

- **`ocaml-arrow`** (Laurent Mazare) — OCaml bindings to Apache Arrow's **C++**
  library, including a ppx for converting OCaml records to and from Arrow
  columns. The author describes it as battle-tested.
- **`polars-ocaml`** (mt-caret) — bindings to **Rust's** Polars, published on
  opam as `polars` and `polars_async`. Polars is a genuine columnar engine:
  Arrow-backed, parallel, SIMD.

So "OCaml has no columnar story" is false. The accurate statement is narrower
and, for this project, sharper: **both are FFI wrappers around another
language's runtime, and neither is usable here.**

`polars-ocaml` targets OCaml 4.14 — OCaml 5 support is blocked upstream in the
Rust interop layer, and its own documentation describes the bindings as work in
progress with expected breakage. This project is OCaml 5.2. It is not a matter
of preference; the binding does not build.

`ocaml-arrow` binds a C++ library, which for a functional-programming exercise
means the columnar half of the pipeline stops being OCaml at the boundary and
becomes a call into C++.

`pgx` — which this project does use, and which is good — is a Postgres
wire-protocol client. It gives you rows, because rows are what the wire
protocol carries.

What does not exist, as far as we can find, is a **columnar store written in
OCaml itself, laid out from a generated schema**. That is the gap this fills,
and the constraint is the point rather than an inconvenience: in a hackathon
about functional programming, "call into Rust" is a strange answer to "how do
you store columns".

The numbers in chapters 9 and 10 are the argument that closing it properly is
worth someone's time: roughly 3× on scans and 14× at the selectivity extremes,
from a store written in a weekend whose layout was derived rather than tuned.

### Where all three fields stop

It is worth stating plainly what this project is not. Columnar storage is a
mature, solved field — Arrow, Parquet, Polars, DuckDB, ClickHouse, decades of
engineering. Schema inference from JSON is a studied problem with published
algorithms. Machine-checked type inference is older still. A weekend of OCaml
improves on none of them, and claiming otherwise would be silly.

They stop at the same place.

**A columnar format takes its schema on faith.** Parquet and Arrow *require* a
schema; neither derives one. And the single most consequential entry in that
schema — whether a column is nullable — arrives from outside. Spark samples
documents and guesses. A hand-written Arrow schema simply declares it. Either
way it is unverified, and it is the flag that decides whether a validity bitmap
is allocated for every row of that column, for the lifetime of the data.

So the nullability bit is simultaneously **the most expensive decision in a
columnar layout and the least checked one**. Wrong permissive: a bitmap per row
nobody needed. Wrong strict: a failed load, or silent corruption in a system
less defensive than this one.

Tatami makes that bit a theorem — `values + nulls + absent = visits` and
`nullable ↔ values < visits` — and then *spends* it on the layout. The mask is
not allocated where the proof says it cannot be needed.

### The part we think is actually new

Nullability analysis is **conservative by nature**. Combine two values that
might be null and a sound analysis must call the result possibly-null. Masks
propagate; a few operations deep, everything is optional again and the analysis
has decayed into uselessness.

That decay does not happen here, because the leaves are *generated* with proved
exact nullability. `ms` is total and `rate` is total, therefore `ms × rate` is
total — not conservatively assumed, provably. The exactness flows downstream
instead of degrading, and the product needs no mask of its own.

That is visible in the measurements: `computed` runs at **3.34×** against
`scan`'s **3.21×** — faster despite doing strictly more work per row, because
neither input nor output carries a check.

A proof about inferred data types, carried through a host language's type
system into a physical memory layout, with the resulting saving measured: that
composition is what we could not find anywhere, and it is the claim we would
defend.

### What is, and is not, new about the proof

An overclaimed novelty is worth less than an accurate one, so this section
states the prior art first.

**Machine-checked type inference is well-trodden.** Algorithm W and the
Damas–Milner system have been mechanised repeatedly — a monadic Coq
formalisation with correctness *and completeness* of inference plus soundness,
completeness and termination of unification; Dubois' ML soundness in Coq;
Naraschewski and Nipkow in Isabelle; CakeML's type inferencer verified in HOL4
as part of an end-to-end verified ML implementation. Completeness of Algorithm
W *is* principality — it computes the most general type. Nothing about proving
principality by machine is novel in itself.

**JSON schema inference already has formal proofs.** Baazizi, Ben Lahmar,
Colazzo, Ghelli and Sartiani's schema inference for massive JSON datasets
(EDBT 2017, extended in the VLDB Journal) ships a companion *Proofs for
parametric schema inference for massive JSON datasets* (2018). Their algorithm
fuses records and marks fields absent from some of them as optional — the same
occurrence-counting territory as chapter 4.5. Those proofs are pen-and-paper
rather than mechanised, but the properties are not new.

**The nearest Lean neighbour proves something else.** `lean4-json-schema`
carries soundness and completeness theorems for JSON Schema *validation* —
that a document satisfies a **given** schema. It does not infer a schema from
data, so it does not speak to principality or to nullability at all.

**What we could not find elsewhere is the link between the theorem and the
bytes.** The nullability result here is not a certificate to be displayed
alongside the code; it is the licence to remove the validity mask from the
physical layout. Without exact nullability you cannot delete the mask, and
deleting the mask is where a large part of both the memory saving (264 MB
against 297 MB) and the scan throughput comes from.

Proof → storage-layout decision → measured benefit is the chain we claim, and
we state it that way deliberately: it is falsifiable, and a reviewer who knows
of prior work joining those three should say so. The weaker claim — "we proved
our inference correct" — would be true and unremarkable.

---

## 12. Limitations

Recorded plainly, because the guarantees above are only worth what their
boundaries are.

- **The shredder is unproved.** Lean describes the tables; OCaml fills them.
  `bin/verify.exe` cross-checks the result against Postgres, which is strong
  evidence but not a theorem. A row-preservation proof is the obvious next
  target and would close the gap between chapters 4 and 6.
- **Id types are manifest, not abstract.** `Run.id`, `Job.id` and `Step.id` are
  all `= int`, so the compiler will not catch a swapped foreign key. Emitting
  them as abstract types is a small change to the generator with a real payoff.
- **The guarantee is conditional on acceptance.** Nothing is proved about
  corpora that inference or generation refuses.
- **Query planning is implied, not implemented.** Chapter 10 shows the curve a
  planner would exploit; no planner consumes it yet.
- **One corpus shape.** Everything is measured on the CI-history corpus. The
  inference is general, but the performance claims are not yet demonstrated
  across dissimilar document shapes.
- **Load time regresses at scale.** See chapter 9 — shredding costs about 30%
  more wall-clock at 200 MB.

---

## 13. Reproducing everything

```sh
docker run --rm -p 8000:8000 -p 8420:8420 durwasa/tatami
```

`:8000` is the demonstration — a document beside the four tables it shreds into,
the corpus queried by both stores, and the measurements charted. `:8420` is the
playground: paste any JSON and read the `.mli` it implies, generated by the real
Lean binary rather than a reimplementation in the page. The image is
`linux/amd64` and `linux/arm64`.

From source:

```sh
lake build tatami                # the generator
lake build Proofs                # the 221 theorems
dune build                       # the servers and stores

dune exec bin/gen_corpus.exe -- --bytes 1.5G --seed 20260914 --out corpus/ci.json
dune exec bin/bench.exe -- --corpus corpus/ci.json --json bench/results.jsonl

./db/up.sh && ./db/load.sh       # postgres, and the shredded tables
dune exec bin/verify.exe         # assert the JSON and the database agree
```

Corpora are deterministic from the seed, so every number in chapters 9 and 10 is
regenerable rather than merely reported.
