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

*Screen: `Proofs/Correctness.lean`, scrolled to `nullability_sound`.*

> Here's why that's safe to rely on. 221 theorems and lemmas, zero `sorry`s.
> They compose into one result, `pipeline_correct`, in five parts.
>
> The one I'd point at is **nullability**.
>
> *Highlight the statement.*
>
> ```
> o.values + o.nulls + o.absent = t.visits
> ∧ (o.nullable = true ↔ o.values < t.visits)
> ```
>
> Every visit to a table is accounted for at every field: a value, an explicit
> null, or an absence. Nothing else. And a field is optional *exactly when* it
> carried a value fewer times than the table was visited.
>
> That matters because absence is computed by truncating subtraction. Without
> the counts identity, a field some document omitted could report zero
> absences, come out non-optional, and we'd emit `string` where the data needs
> `string option`. That code compiles. The store does catch it — it aborts and
> names the column — but at load time, on real data, in code the compiler
> already accepted. The theorem makes that situation impossible instead.
>
> *Scroll to `schema_canonical`.*
>
> And this one: shuffle the corpus, get an **equal** schema. Not equivalent —
> equal. Which is why two runs of the generator agree byte for byte.

---

## 3:00 — The payoff in the code (45s)

*Screen: `lib/columnar/columnar.ml`, the header comment.*

> Now the payoff. One dense typed array per column. The array's type comes from
> the `.mli` and from nowhere else.
>
> *Highlight:* "a validity mask is allocated only where that layout says
> `option`."
>
> So a column the contract calls total has **no mask, no branch, and no memory
> holding either**. That's only sound because of the theorem we just looked at.
> The proof isn't decoration, it's what lets us delete the mask.
>
> The numbers, measured on this machine. A dense `int` column is 8 bytes an
> element, so a 128-byte line carries sixteen values and every byte fetched is
> one the query wants. The same field in the row store is one of five in a
> 48-byte record reached through a pointer, so 56 bytes an element, and about
> one byte in six that you fetch is the one you asked for.
>
> And if you gave up and made everything `int option`: 24 bytes an element,
> because `Some` is a heap block, 16 bytes, and the array holds the pointer to
> it. Three times the traffic and a dependent load per element. Even the honest
> encoding of a nullable column, dense values beside a mask, is 16 bytes an
> element. Two times, plus a branch per row.
>
> That is the cost of not knowing, and it is per row, forever.

---

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
