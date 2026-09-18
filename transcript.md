# tatami — 5 minute demo transcript

*Roughly 1021 spoken words. Screen directions in italics. Timings are targets,
not a script to race against.*

---

## 0:00 — The problem (45s)


> Let us say we have a collection of JSON documents for example we have data for a CI service's build history. 
> Repos contain runs, runs
> contain jobs, jobs contain steps, and we don't have a predetermined SCHEMA.
>
> I want it in typed columnar tables. Tables query faster than documents, and
> for scans a columnar layout has been the known answer for decades. 
>
> What we built is the path between the two, and it is three pieces. **Lean 4
> infers the schema and proves the inference correct.** It then **generates the
> OCaml**: a signature per table, and the loader that streams the documents into
> tables and into Postgres. And then we **benchmarked** it.
>

---

## 0:30 — The playground (45s)

*Screen: browser, `localhost:8420`. "null and absence"

Given a json document wer are generating equivalent .mli file which is an interface file for OCaml.

Here we have an example where the key x is there in every document; every document is represented as a value in an array.
the key y is null and int so we infer the type option int whereas the key z does not have a value in each of the document 
so we cannot infer its type so its unit option.

>
> And nothing here is built for that one corpus. Different shape, nested object,
> two arrays, a map, and you get a different set of tables out. The theorem is
> quantified over *any* list of documents. 
---

## 1:15 — Why an .mli (35s)

*Screen: editor, `runs_jobs_steps.mli`.*

> Why a signature file? Because an `.mli` is a **contract** — it's what sits on
> a boundary and says exactly what crosses it.
>
> We learn the table's columns, their types, the column `error` is
> a column that can be null, its string option because error has a string message in the corpus, and the foreign key, expressed
> as a function. The  data has become something the OCaml compiler
> enforces, instead of a JSON schema document some loader interprets at
> runtime.

---

## 1:50 — The proof (70s)

Tatami proof script
Tatami infers a database schema from schemaless JSON. Why trust it? Because the OCaml signature we generate is a contract. And since we generate it rather than write it, we can prove things about the generator. It all comes down to one theorem.
[open Proofs/Correctness.lean:148, point at it]
Here it is. If Tatami accepted your data and produced a schema, this guarantees five things. One. The names it makes are always legal, and no two things end up with the same name. Two. Run it twice on the same data in a different order, and you get the exact same answer. Three. The shape comes through. If your JSON nests jobs inside runs, the generated code nests them the same way. Four. Every field gets the tightest type that still fits all the data. And five, a field is optional exactly when some record was missing it. That's the claim. Here's where it's proved.
[show the files in the Proofs/ folder in VS Code]
That's twelve files, and they're all about two questions. Is the schema right? And does the generated code say so? Correctness.lean is the one we were just in, the five I've described. Counts.lean is the counting behind 'optional'. Inference.lean is where order stops mattering, and where the types come out as tight as they go. Lattice.lean proves joining two types is well defined in the first place. Mangle.lean is the renaming: a JSON field name becomes an OCaml one without two names ever turning into one. Merge.lean shows combining two documents works either way round. Tree.lean is the nesting surviving into the modules. Walk.lean keeps everything sorted as it reads. Wellformed.lean is the check behind number one. And the rest prove the conditions those depend on.
[show the output of lake build on a terminal]
And it all builds. Two hundred and twenty-three theorems, and we have proved all of them in Lean4.




---

## 3:00 — Why the layout wins (75s)

*Screen: `lib/rowmajor/records.ml`, the `type step` declaration.*

> The row-major store's step record. Five fields. Every OCaml heap block carries
> a one-word header and every field takes one word whatever it holds, so six
> words at eight bytes: **48 bytes** a record.
>
> And a step array is an array of *pointers*, so per element add the eight-byte
> slot in the array. **56 bytes an element.**
>
> To sum `ms` you load a pointer, dereference it, and pull the cache line
> holding the block. This machine's line is 128 bytes and a block is 48, so one
> line gives you **two or three records. Call it under three values a line**, and
> about twenty-one of the hundred and twenty-eight bytes you fetched are `ms`.
> The rest is header, name, rate and error, which this query never reads.

*Screen: `lib/columnar/columnar.ml`, the `scan` loop.*

> Same query, columnar. `ms` is an `int array`, and an OCaml int is immediate:
> it lives in the array word. No block, no pointer. Eight bytes an element, so
> one 128-byte line carries **sixteen values, and every byte of it is a value
> you want**. Under three against sixteen, for the same question.
>
> Both stores know `ms` is an int and cannot be null. The record store's types
> are hand-written and just as good. Only the layout differs, and that is the
> three times.

*Screen: back to `schema/step.mli`.*

> So why not skip inference and make every column `int option`? Because on a
> scalar, `option` is a boxing. `Some` is a sixteen-byte block and the array
> holds a pointer to it: **24 bytes an element**, and an indirection before you
> see the number. Even the honest encoding, a dense column beside a mask, is
> sixteen bytes and a branch on every row.
>
> That is the cost of not knowing, and you pay it per row for the life of the
> data.

## 3:45 — The measurements (60s)

*Screen: browser, `localhost:8000`, the charts tab.*

> Five queries, three stores: raw Yojson, a row-major record store, and the
> columnar one. Every answer is compared before any timing is believed; the
> harness prints "timings are meaningless" if the stores disagree. They don't.
>
> All of this is one machine, a MacBook Pro with an Apple M2 Pro: ten cores,
> six performance and four efficiency, 16 GB, 64 KB of L1 data cache, 4 MB of
> L2, and **128-byte cache lines**. OCaml 5.3. Five repeats a point. The cache
> line matters for the next number, so it is worth saying out loud: a dense
> `int` column puts **sixteen** values on one line, not eight.
>
> Scans get about **three times** faster. The computed query — `sum(ms × rate)`
> — about three and a half.
>
> *Point at `document` and `three_hop`.*
>
> And these two go the *other* way. That's deliberate. `document` is the case a
> row store exists for. If columns won that one too, the benchmark would be
> wrong somewhere.
>
> We're not claiming we built a faster database. We're claiming something more
> useful: **once the type is known, you can predict which queries get faster** —
> from the schema, before reading a row.
>
> *Screen: the selectivity sweep.*
>
> And here's the shape a planner would want. Sweep the predicate threshold: at
> 0.02% selectivity, fourteen times. At full scan, fifteen. In the middle,
> three. A U-curve — and the schema already says which columns are scannable
> and which are nullable.

---

## 4:45 — Close (25s)

> Two things I'd leave you with.
>
> One: columnar storage is solved — Arrow, Parquet, Polars. We haven't improved
> on any of it. But every one of them takes the schema *on faith*. Arrow and
> Parquet require a schema; they never derive one. And whether a column is
> nullable — the bit that decides if a validity bitmap gets allocated for every
> row, forever — is guessed upstream by sampling, or declared by hand.
>
> We made that bit a theorem, and then spent it on the layout.
>
> Two: it's functional the whole way down. Lean 4 for inference and proof,
> OCaml for loading, storage and measurement. The one place correctness truly
> had to be guaranteed is the one place we could hand to a theorem prover.
>
> `docker run -p 8000:8000 -p 8420:8420 durwasa/tatami`. Both ports, one
> command.

---

## Shot list

| Time | Screen           | Have ready beforehand                                    |
|------|------------------|----------------------------------------------------------|
| 0:00 | terminal         | `head -c 400 corpus/small.json`                          |
| 0:30 | `localhost:8420` | JSON with `qty`/`price`/nullable `note` in the clipboard |
| 1:15 | editor           | `schema/step.mli`                                        |
| 1:50 | editor           | `Proofs/Correctness.lean` at `nullability_sound`         |
| 3:00 | editor           | `lib/columnar/columnar.ml` header                        |
| 3:45 | `localhost:8000` | charts tab, then the sweep                               |
| 4:45 | terminal         | the `docker run` line                                    |

Start the container before recording — the first run pulls ~118 MB, and the
backend spends a moment loading the corpus.
