# tatami — spoken introduction

*Front end first, then the back end, then the numbers, and the proof last.*

---

## 1. What it is

Hello everyone.

We've built a tool that shreds schema-less JSON into queryable tables — rows
and columns — and the thing that makes it work is that it doesn't guess. It
infers the types from the documents you give it, and writes them out as an
OCaml signature file.

---

## 2. The front end

So let me start with what you can actually touch.

This is the playground. You paste your JSON in here — any JSON, not ours — and
on the other side you get an `.mli` back. That's OCaml's interface file, and
for our purposes it's a **contract**. A contract between the model and the data
plane.

And you can read it straight off. Every column, its type, and crucially which
ones can be null and which can't. That last part is the whole game, and I'll
come back to it.

---

## 3. The back end

Now, from that same `.mli` we also generate a loader. That's the ETL piece: it
takes the documents, shreds them into four tables, and ingests them. It talks
to Postgres through `pgx`, which is a Postgres client written in OCaml, and it
generates the DDL too — so the tables you're looking at here were created from
the same inferred schema.

And here's the design decision I'd like you to notice.

**The query system's decisions come from the `.mli` files.** Whether a column
gets a validity mask, what array type it gets, which plan a join uses — all of
that is read off the signature. **Nothing is based on cardinality or
selectivity.** We never count how many rows match a predicate, never build a
histogram, never sample. That would mean sneaking a look at the data, and then
the schema wouldn't be the thing deciding any more.

There's one place we do read the data, and I'd rather point at it than have you
find it. When we shred, we walk documents depth-first, so every run of one repo
lands before any run of the next — which means a parent's children occupy one
contiguous block of rows. We check that as we build, by walking the key column.
And it lets a join stop being a scan and become a slice.

But that isn't a statistic either. It follows from the relationship having been
an *array* in the source document, plus the order we visit in. A database would
need an index or a CLUSTER to know the same thing. And we check it rather than
assume it — if any parent's rows turn out to be interrupted, we throw the
slices away and fall back to scanning.

---

## 4. Why that's worth anything

Let me show you what the types buy, with a query.

`select ms from step`. In the row-major store, a step is a record. Five fields
plus a header, and the array holds a pointer to each — so **56 bytes an
element**. The cache line on this machine is 128 bytes, so one line gives you
roughly **three records**, and you only wanted one field out of each.

In the columnar store, `ms` is an `int array`. And because the inference proved
that column is never null, it's an immediate `int` — the value lives in the
array word itself, eight bytes. So one 128-byte line carries **sixteen values**,
and every byte of it is something the query asked for.

**Sixteen against three.** Same question, same data, same type information on
both sides. Only the layout differs.

Now — we could have inferred `int option` instead, and it's worth seeing what
that costs. In OCaml a `Some` is a block on the heap, so the array holds a
pointer to it: twenty-four bytes an element, about **five values** a line, plus
an indirection before you see the number. Still better than row-major. Nowhere
near an immediate `int`.

And it compounds. Take `ms × rate`. Because the lattice gave us `int × float`
rather than `int option × float option`, there's no mask on either input and no
mask on the result, so the arithmetic runs straight down two dense arrays.

Our theory is that statistical queries — sums, counts, thresholds — usually
touch one or two columns over many rows, and that's exactly the shape columns
are good at.

---

## 5. Where we lose

But I want to be straight about the other direction.

We lose on `document`. And we should — records were *made* for documents. A
record store already holds everything about one repository together, whereas we
have to go and collect it from separate tables. Same for the three-level join,
which for us becomes nested iteration across columns.

**So we're not claiming our implementation is faster.** What we observe is that
some queries run faster columnar and some run faster row-major.

Which is the interesting part, because it turns into a *decision* problem. Given
a pool of queries, some should go to rows and some to columns, and the schema
tells you which — before you read a single row. And if the same column keeps
coming back with `qty > 10`, `qty = 2`, `qty < 10`, you get better and better
value out of that layout. Interleave queries touching other columns and you can
club them together. Those tricks are all available once the types are the thing
deciding.

---

## 6. Do we believe the numbers?

Only if they survive a check.

We have three stores answering the same five questions — raw Yojson, row-major
records, and the columnar one. Yojson is our **oracle**. It keeps nothing, it
re-walks the document every single time, and it takes its own sweet time about
it. But it shares no machinery with the things under test, so if anything is
wrong, it disagrees.

And separately we check the database: the same aggregates computed twice, once
by streaming the JSON and once in SQL, at every level of the nesting.

If any of that disagrees, the harness refuses to print the timings at all.
Benchmarking only means something after differential testing passes.

---

## 7. And the proof

Which brings me to the last thing.

Everything I've just shown you rests on one step being right: the conversion
from schema-less JSON to that `.mli`. If the inference says a column is never
null and it's wrong, we've deleted a mask we needed. So that step is the one we
proved.

**Two hundred and twenty-three theorems in Lean 4**, and they compose into a
single result. Given a corpus we accepted: the signature is well formed, the
schema doesn't depend on the order the documents arrived in, the nesting in
your JSON is the nesting in the generated modules, every type is the tightest
one that still fits the data, and a column is optional **exactly** when some
document was missing a value there.

That last one is what licenses everything in section four.

Thank you.
