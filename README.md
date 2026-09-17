# tatami

**Derive a typed columnar schema from schemaless JSON — and prove the derivation is right.**

You are handed a pile of JSON. Nobody wrote down what shape it is. You want it
in tables, you want the types to be correct, and you want to know — not hope —
that the types you inferred actually describe the data.

Tatami does that, end to end, in functional languages: **Lean 4 infers the
schema and proves it correct; OCaml streams the data into typed columnar
tables and measures what the typing bought.**

---

## The idea in one paragraph

An `.mli` file is a *contract*. It sits on the boundary between two pieces of
code and says exactly what crosses it. Tatami's claim is that this contract is
the right place to put an inferred schema: instead of a JSON schema document
that some loader interprets at runtime, the inferred shape becomes an OCaml
signature the compiler enforces. And because the signature is *generated*, not
written by hand, we can prove things about the generator — so the contract is
not merely checked, it is earned.

```
schemaless JSON  ──▶  Lean 4  ──▶  .mli + .ml  ──▶  OCaml loader  ──▶  typed columns
                   (infers &        (the            (streams,          (the payoff:
                    proves)          contract)       keeps refs)        typed scans)
```

---

## What actually happens, step by step

**1. Read the documents.** The corpus is a CI service's build history: repos
contain runs, runs contain jobs, jobs contain steps. Four levels, every level
an array. Nothing declares the shape.

**2. Infer the schema (Lean).** Lean walks the documents and, for every field
it sees, computes the *principal* type — the least type that admits every
value observed. It counts, per field, how many times a value was present, how
many times it was explicitly `null`, and how many times it was absent
entirely. A field is optional exactly when those counts say it was missing at
least once.

**3. Emit the contract (Lean).** Lean writes one `.mli` per table, plus the
`.ml` implementations and a loader. This is generated OCaml — the plumbing of
the data pipeline, written by a theorem prover:

```ocaml
(* step.mli — generated *)
type t
type id = int
val make : id:int -> job_id:Job.id -> idx:int ->
           error:string option -> ms:int -> name:string -> rate:float -> t
val of_job : Job.id -> t list       (* the foreign key, as a function *)
val error  : t -> string option     (* the ONLY optional field here *)
val ms     : t -> int               (* not int option — the data never lacked it *)
val rate   : t -> float
```

Read that signature and you know the table: its columns, their types, which
single column can be null, and how it links to its parent. `idx` is kept
because order is information the JSON array carried and a table would lose.

**4. Load it (OCaml).** A streaming loader shreds documents into four tables —
`repo`, `run`, `job`, `step` — preserving referential integrity: every child
row records the parent it came from and the position it held. The same loader
populates Postgres through `pgx`, so the same data exists relationally and can
be cross-checked with SQL.

**5. Store it columnar (OCaml).** One dense typed array per column. The array's
type comes from the `.mli` and from nowhere else. **A validity mask is
allocated only where the signature says `option`** — so a column the contract
calls total has no mask, no branch, and no memory holding either. Nothing is
special-cased by column name.

**6. Measure it (OCaml).** Five queries, answered by three stores — raw
Yojson, a row-major record store, and the columnar store. Every answer is
compared before any timing is believed.

---

## Why the proof matters

Step 5 is the whole payoff, and it rests entirely on step 2 being right.

If inference wrongly decides a column is total when some document lacked a
value, the columnar store allocates no mask — and the generated OCaml compiles
cleanly and then fails on the first document missing that field, with nothing
to say what went wrong. A wrong `option` in the other direction is cheaper but
still costs a mask, a branch, and the memory to hold them, on every row,
forever.

So we proved it. **221 theorems and lemmas, zero `sorry`s.** They compose into
a single top-level result, `pipeline_correct`, in five named parts:

| Part | What it says |
|---|---|
| **Well-formedness** | The emitted signature is legal OCaml: no repeated module name, value name, or record field. |
| **Canonicity** | The schema depends on the corpus *as a set of documents*, not on arrival order. Shuffle the input and the output is **equal**, not merely equivalent — which is why two runs agree byte for byte. |
| **Structure preservation** | The tree the documents induce and the graph in the generated signatures are the *same graph*: no edge lost, none invented, distinct tables get distinct modules, and the graph is rooted — so no table is declared that the loader would create and never fill. |
| **Principality** | Every field gets the least type admitting all values seen. Adequacy alone is nearly free (`float` describes integers; so does `int option`); minimality is what rules the loose answers out. |
| **Nullability** | `values + nulls + absent = visits`, and `optional` is set precisely when `values < visits`. The `option` is neither missing nor gratuitous. |

It is equally worth saying what the proof does **not** claim. Every part is
conditional on inference and generation both succeeding — both refuse inputs,
and the guarantee is about what is *emitted*, not what is accepted. And it says
nothing about rows: Lean describes the tables, the OCaml loader fills them, and
that shredder is outside what Lean sees.

---

## What the measurements show

Five queries, three stores, corpora from 10 MB to 200 MB. **All three stores
return identical answers** — the harness counts disagreements and prints
*"timings below are meaningless"* if there are any. There are none.

Columnar vs. the row-major record store (higher = columnar faster):

| Query | What it does | Speedup |
|---|---|---|
| `scan` | count steps longer than *n* — one column of ten | **2.9× – 3.3×** |
| `computed` | `sum(ms × rate)` over those steps — two columns, arithmetic | **3.2× – 3.5×** |
| `by_status` | longest step per status — five groups over the table | 1.24× – 1.28× |
| `three_hop` | step → job → run → repo, for one org | 0.38× – 1.20× |
| `document` | everything under one repo | 0.46× – 0.81× |

**We are not claiming the columnar store is faster.** Two of the five queries
go the other way, by design — `document` is the case a row store exists for,
and if columns won that one too the benchmark would be wrong somewhere. The
claim is narrower and more useful: *once the type is known*, the queries that
touch few columns over many rows get substantially faster, and you can predict
which ones from the schema alone.

Against raw Yojson document traversal, both typed stores are **50× – 500×**
faster on scans, and effectively unbounded on keyed lookup.

Memory: the columnar store is consistently smaller — 264 MB vs 297 MB on the
200 MB corpus — because total columns carry no validity mask.

### Selectivity is where it gets interesting

Sweeping the threshold of `scan` across a 50 MB corpus:

| Rows kept | Speedup |
|---|---|
| 0.02% | **14.1×** |
| 3.8% | 9.0× |
| 19% | 4.9× |
| 54% | 3.4× |
| 98% | 13.4× |
| 100% | **15.3×** |

A U-curve. Highly selective predicates and full scans both do very well; the
middle is where per-row branching costs most. This is exactly the shape a
query planner would want to know about — and *the schema already tells it
which columns are scannable and which are nullable*, before a single row is
read.

---

## Two things that make this unusual

**1. The proof is spent, not displayed.** Be precise about what is and is not
new here. Machine-checked *type* inference is well-trodden — Algorithm W has
been mechanised in Coq, Isabelle and HOL4, and completeness of Algorithm W
already *is* principality. JSON schema inference has formal proofs too:
Baazizi, Colazzo, Ghelli and Sartiani give pen-and-paper proofs for parametric
schema inference, occurrence-counting for mandatory versus optional fields
included. And the nearest Lean neighbour, `lean4-json-schema`, proves
*validation* — that a document satisfies a **given** schema — not inference
from data.

What we have not found elsewhere is the link between the theorem and the
bytes. The nullability result is not a certificate to display; it is the
licence to **delete the validity mask from the physical layout**, and the
saving is measured (264 MB against 297 MB). Proof → storage-layout decision →
benchmark is the chain we believe is new, and it is the one worth arguing
about.

**2. OCaml has no columnar story, and we built one.** There is no Arrow
binding, no Parquet reader, no columnar engine for OCaml. `pgx` — which we use,
and which is good — is a Postgres wire-protocol client: it gives you rows. If
you want dense typed columns in OCaml today, you write them. So we did, driven
entirely by generated types, and measured the result. The absence is the
opportunity: the numbers above are an argument that this gap is worth closing.

The whole pipeline is functional end to end — Lean 4 for inference and proof,
OCaml for loading, storage, querying and measurement. No imperative escape
hatch in the middle, and the one place where correctness actually had to be
guaranteed is the one place we could hand to a theorem prover.

---

<details>
<summary><strong>Run it</strong> — one command, two servers</summary>

```sh
docker run --rm -p 8000:8000 -p 8420:8420 durwasa/tatami
```

- **<http://localhost:8000>** — the demonstration. One document beside the four
  tables it shreds into, the corpus queried by both stores side by side, and
  the measurements charted.
- **<http://localhost:8420>** — the playground. Paste any JSON, read the `.mli`
  it implies. `/translate` reaches the real Lean generator, not a
  reimplementation in the page.

A 1,000-repo corpus is baked in, so that command needs no arguments and no
network. The image is `linux/amd64` and `linux/arm64`; Docker picks from the
manifest.

For a larger corpus, generated at startup from the same seed:

```sh
docker run --rm -p 8000:8000 -p 8420:8420 -e TATAMI_ROWS=50000 durwasa/tatami
docker run --rm -p 8000:8000 -p 8420:8420 -e TATAMI_BYTES=200M durwasa/tatami
```

Different host ports — change the left side only; the right side is fixed
inside the image:

```sh
docker run --rm -p 9000:8000 -p 9420:8420 durwasa/tatami
```

</details>

<details>
<summary><strong>Build it</strong> — multi-architecture image</summary>

```sh
docker buildx build --builder multiarch \
  --platform linux/amd64,linux/arm64 \
  -t durwasa/tatami:latest \
  --push .
```

Three stages: the Lean generator, the OCaml servers, and a slim runtime
carrying only the two binaries and the pages. The build asserts the generator
answers before shipping it, in both architectures. Plain `docker build` carries
only the architecture it was built on and fails with `exec format error`
anywhere else.

</details>

<details>
<summary><strong>Without Docker</strong> — building from source</summary>

Needs OCaml 5.2 and the Lean toolchain named in `lean-toolchain`.

```sh
lake build tatami                # the generator + the proofs
dune build                       # the servers and stores
dune exec bin/serve.exe          # localhost:8000
python3 dev/serve.py             # localhost:8420
```

Generate a corpus and benchmark it:

```sh
dune exec bin/gen_corpus.exe -- --bytes 1.5G --seed 20260914 --out corpus/ci.json
dune exec bin/bench.exe -- --corpus corpus/small.json --json bench/results.jsonl
```

`corpus/small.json` is checked in — 1,000 repos, 7.2 MB: 2,511 runs, 5,074
jobs, 17,744 steps. Larger corpora are not, because they are deterministic
from the seed and regenerating beats copying. At 1.5 GB the corpus is large
enough that `JSON.parse` will die on it, Node's maximum string length being
smaller than the file; use a streaming reader (`lib/corpus.ml` in OCaml,
`ijson` in Python, `stream-json` in JS).

</details>

<details>
<summary><strong>Check it against SQL</strong> — the relational half</summary>

The part the browser tabs do not show: shred the same corpus into Postgres and
assert the two stores agree.

```sh
./db/up.sh                      # postgres on 5432, safe to run repeatedly
./db/load.sh                    # shred the JSON into the four tables
dune exec bin/verify.exe        # assert the JSON and the database agree
```

</details>

<details>
<summary><strong>Check the proofs</strong></summary>

```sh
lake build Proofs
```

221 theorems and lemmas, zero `sorry`s. The top-level statement is
`pipeline_correct` in `Proofs/Correctness.lean`, which groups the five parts so
the guarantee can be read without opening nine files.

</details>

---

## Layout

```
Main.lean  Tatami.lean  Tatami/    the generator: inference and .mli emission
Proofs.lean  Proofs/               what is proved about it
schema/                            the .mli/.ml files Lean emits, and the loader
lib/  bin/                         the OCaml stores, servers and benchmarks
web/  dev/serve.py                 the pages, and the playground server
examples/                          inputs worth reading whole, and their .mli
db/  schemacheck/  test/  bench/   postgres, schema checking, tests, timings
```
