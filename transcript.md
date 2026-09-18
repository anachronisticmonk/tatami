# tatami — demo transcript

*Presenter notes. Italics are what's on screen, quoted blocks are what you say.
Timings are targets, not a metronome. Read it aloud once before the take, and
anything that trips your tongue, change it.*

---

## 0:00 — The problem (45s)

*Screen: terminal, the first few hundred bytes of `corpus/small.json`.*

> So let's say we have a collection of JSON documents. In our case it's data for
> a CI service's build history, so repos contain runs, runs contain jobs, and
> jobs contain steps. And crucially, there's no predetermined schema. Nobody
> wrote one down; there is no SCHEMA.
>
> Now what I actually want is this in typed columnar tables. And the reasoning is
> : tables query faster than documents, and for scans, a columnar
> layout has been the known answer for decades.
>
> So what we built is the path between those two. And it's three pieces. First,
> **Lean 4 infers the schema, and proves the inference correct**. Then it
> **generates the OCaml** for us: a signature per table, plus the loader that
> streams the documents into tables and into Postgres. And then finally, we
> **benchmarked** it.

---

## 0:45 — The playground (45s)

*Screen: browser, `localhost:8420`, with the "null and absence" document ready
to paste.*

> Right, so this is the playground. Given a JSON document, we generate the
> equivalent `.mli` file, which is just the interface file for OCaml.
>
> And here we have an example. Every document is a value in an array, and the
> key `x` is there in every single document, so that one's easy.
>
> Now the key `y` is sometimes null and sometimes an int, so we infer the type
> `int option`. Whereas the key `z` doesn't have a value in *any* of the
> documents, so there's nothing to infer a type from at all, and you get
> `unit option`.
>
>
> And nothing here is built for that one corpus. You can paste your own json;  different shape,
> nested object, couple of arrays, a map, and you get a different set of tables
> out. The theorem is quantified over *any* list of wellformed json.

---

## 1:30 — Why an .mli (35s)

*Screen: editor, `runs_jobs_steps.mli`.*

> So why a signature file? Well, because an `.mli` is a **contract**. It's the
> thing that sits on a boundary and says exactly what crosses it.
>
> And you can just read it off. We learn the table's columns, we learn their
> types. So let's say the column `error` is a column that can be null: it comes
> out as `string option`, because error carries a string message in the corpus.
> And the foreign key is there too, expressed as a function.
>
> So the data has become something the OCaml compiler enforces, instead of a
> JSON schema document that some loader interprets at runtime.

---

## 2:05 — Why the layout wins (75s)

*Screen: `lib/rowmajor/records.ml`, the `type step` declaration.*

> Okay, so this is the row-major store's step record. Five fields.
>
> Now, every OCaml heap block carries a one-word header, and every field takes
> one word whatever it holds. So that's six words, at eight bytes a word, which
> gives you **48 bytes** a record.
>
> And a step array is an array of *pointers*, so per element you also add the
> eight-byte slot in the array. So, **56 bytes an element**.
>
> Now, to sum `ms`, you load a pointer, you dereference it, and you pull the
> cache line holding the block. And this machine is a MacBook Pro M2, so the
> cache line is 128 bytes, and a block is 48. Which means one line gives you two
> or three records. Call it **under three values a line**.

*Screen: `lib/columnar/columnar.ml`, the `scan` loop.*

> Same query, columnar. Here `ms` is an `int array`, and an OCaml int is
> immediate, so it lives in the array word itself. Eight bytes an element. So one
> 128-byte cache line carries **sixteen values, and every byte of it is a value
> you want**.
>
> So that's **under three, against sixteen**.
>
> And here's the thing: both stores know `ms` is an int and cannot be null. The
> record store's types are hand-written, and they're just as good. Only the
> layout differs.

*Screen: back to `schema/step.mli`.*

> So then, why not skip the inference and just make every column `int option`?
>
> Because on a scalar, `option` is a boxing. `Some` is a sixteen-byte block, and
> the array holds a pointer to it. So that's **24 bytes an element**, and an
> indirection before you even see the number. You end up with around 5.3 values
> a line. Which is better than row-major, sure, but we get more performance from
> knowing the type is `int` instead of an `int option`.
>
> And that's the cost of not knowing. And you pay it per row, for the life of
> the data.

---

## 3:20 — The measurements (60s)

*Screen: browser, `localhost:8000`, the performance tab.*

> So we're running five queries across three stores: raw Yojson, a row-major
> record store, and the columnar one. And we treat raw Yojson as an oracle,
> because timings and measurements only matter if the query passes differential
> testing first.

*Screen: terminal. Run the two greps below, one after the other. Optional, but
it answers the obvious objection before anyone raises it.*

```
$ grep -n "Yojson\|member\|to_int" lib/columnar/columnar.ml | tail -1
253:let opt_int b k j = match member k j with `Int x -> put_int b x | _ -> put_null b

$ grep -n "^let scan\|^let computed\|^let three_hop" lib/columnar/columnar.ml
334:let scan t threshold =
345:let computed t threshold =
457:let three_hop t org =
```

> And one thing worth heading off. Yojson shows up in all three stores, so let
> me be precise about where. In the columnar store the last Yojson call is on
> line 253, and that's inside `load`. The first query doesn't start until line
> 334. So JSON is parsed once, on the way in, and after that nothing in the
> query path touches it. Same story in the record store: Yojson ends at line 64,
> queries start at 117.
>
> The only store that calls Yojson per query is the oracle, and that's the whole
> point of it.

>
> And all of this is one machine, by the way. A MacBook Pro with an Apple M2
> Pro: ten cores, six performance and four efficiency, 16 gig, 
> and **128-byte cache lines**. OCaml 5.3. So as we said, a
> dense `int` column puts **sixteen** values on one line.
>
> Scans come out about **three times** faster. And the computed query, that's
> `sum(ms × rate)`, about three and a half.

*Point at `document` and `three_hop`.*

> Now, we also have two queries, `document` and `three_hop`, where the row-major
> store beats the column-major one. So these two go the *other* way.
>
> And `document` is really the case a row store exists for. That's primarily
> because a join at the record level already gets all the required data sitting
> right there, whereas in contrast the columnar store has to hop around between
> tables to get the data the join asked for.
>
> And moreover, we don't want to optimise the query based on the cardinality of
> the table, because that would mean sneaking into the data, and that defeats
> the purpose. We want all the optimisations to happen strictly based on the
> `.mli` file.



---

## 4:20 — The proof (95s)

*Screen: talking head, or hold the previous frame.*

> So, Tatami infers a database schema from schemaless JSON. Why trust it?
>
> Well, because the OCaml signature we generate is a contract. And since we
> *generate* it rather than write it, we can prove things about the generator.
>
> And it all comes down to one theorem.

*Screen: open `Proofs/Correctness.lean` at **line 148**, `pipeline_correct`.
Point at it.*

> So here it is. If Tatami accepted your data and produced a schema, this
> guarantees five things.
>
> **One.** The names it makes are always legal, and no two things end up with
> the same name.
>
> **Two.** Run it twice on the same data in a different order, and you get the
> exact same answer.
>
> **Three.** The shape comes through. So if your JSON nests jobs inside runs,
> the generated code nests them the same way.
>
> **Four.** Every field gets the tightest type that still fits all the data.
>
> **And five,** a field is optional exactly when some record was missing it.
>
> So that's the claim. Now here's where it's proved.

*Screen: the `Proofs/` folder in VS Code, all twelve files visible. Highlight
each as you name it.*

> So that's twelve files, and they're all really about two questions. Is the
> schema right? And does the generated code say so?

| highlight          | say                                                                                               |
|--------------------|---------------------------------------------------------------------------------------------------|
| `Correctness.lean` | is the one we were just in, the five I've described.                                              |
| `Counts.lean`      | is the counting behind 'optional'.                                                                |
| `Inference.lean`   | is where order stops mattering, and where the types come out as tight as they go.                 |
| `Lattice.lean`     | proves joining two types is well defined in the first place.                                      |
| `Mangle.lean`      | is the renaming: a JSON field name becomes an OCaml one, without two names ever turning into one. |
| `Merge.lean`       | shows combining two documents works either way round.                                             |
| `Tree.lean`        | is the nesting surviving into the modules.                                                        |
| `Walk.lean`        | keeps everything sorted as it reads.                                                              |
| `Wellformed.lean`  | is the check behind number one.                                                                   |

> And then the rest prove the conditions those ones depend on.


> And it all builds. Two hundred and twenty-three theorems, and we have proved
> all of them in Lean 4.

---

## 5:55 — Close (25s)

*Screen: terminal, ready to run the container.*

> So, two things I'd leave you with.
>
> One: columnar storage is solved. We are inferring types from the data, and providing a formal proof of its conversion 
> to .mli files.
>
> We made that bit a theorem, and then we spent it on the layout.
>
> And two: the entire machinery is functional the whole way down. Lean4 for inference and proof,
> OCaml for loading, storage and measurement. The one place correctness truly
> had to be guaranteed is the one place we could hand to a theorem prover.
>
> And that's it. `docker run -p 8000:8000 -p 8420:8420 durwasa/tatami`. Both
> ports, one command.
