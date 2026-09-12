# Reading the Lean implementation

1489 lines across twelve files. Here is the order to read it in — each step
answers one question, and most have something you can run.

---

## Step 0 — Watch it work before reading anything

```bash
lake build
echo '{ "a": 1, "b": { "c": 1, "d": 2 } }' | ./.lake/build/bin/tatami
echo '{ "xs": [ {"n":1}, {"n":2} ] }'      | ./.lake/build/bin/tatami
echo '{ "a": 1, "a": 2 }'                  | ./.lake/build/bin/tatami
```

Ten minutes of this and the rest of the code has somewhere to attach. You will
see the three shapes it produces — a plain module, a `module rec` group, and a
rejection.

## Step 1 — The spine: `Main.lean:12`, `pipeline`

Twelve lines, and the whole program is in them:

```
text → Doc.parse → documents → inferCorpus → toSchema → gen → File.print → text
```

Everything else is one of those five stages. Read `main` at `:66` too — it is
just argument handling and the two output modes.

**Do not read anything else until this diagram is in your head.** The rest of
the codebase makes no sense without it, and makes near-total sense with it.

## Step 2 — The shape of the codebase

Three groups, and the split is the thing to internalise:

| | knows about |
|---|---|
| `Doc`, `Path`, `Ty`, `Infer`, `Config` | **JSON only** — never mentions OCaml |
| `Ocaml`, `Print` | **OCaml only** — never mentions JSON |
| `Gen` | the only file importing from both |
| `Schema` | what `Gen` receives — 28 lines, read it now |

`Schema.lean` is the hinge. Read all 28 lines: `Column`, `Table`, `Schema`.
That is the entire vocabulary the two halves share.

## Step 3 — Types and the join: `Ty.lean` (68 lines)

The smallest file with real content, and the one the proofs are about.

- `Ty` at `:16` — six constructors. Note `ref` and `coll` carry a `Path`: a
  nested object and a collection have no type of their own, only a pointer to
  their table.
- `Field` at `:39` — nullability is a *flag*, not a type.
- **`Ty.join` at `:49`** — the heart of inference. Read every case.

Then make a scratch file and poke at it:

```lean
import Tatami
open Tatami
#eval Ty.join .int .float     -- some Ty.float
#eval Ty.join .int .str       -- none        ← this is the rejection
#eval Ty.join .bot .bool      -- some Ty.bool
```

## Step 4 — Inference: `Infer.lean` (245 lines, the biggest)

Read in this order, not top to bottom:

1. **`Obs` at `:44`** — what is accumulated per member. Look at the three counts.
2. **`TableObs` at `:68`** — what is accumulated per table. Short, and the
   docstring above it is the important part: nothing here records where a row
   came from, because a table's path already says.
3. **`seeScalar` at `:22`** — one value → one type. Note it never sees objects
   or arrays; the caller handles those because only the caller knows the path.
4. **`recordMember` at `:117`** — where the join is actually called, and where
   a conflict is thrown.
5. **The walk**, four mutually recursive functions rather than one:
   `observeObject` at `:155` registers a visit and hands off; `observeMembers`
   at `:169` is the interesting one — it dispatches on what each member *is*;
   `observeElems` at `:216` and `observeEntries` at `:240` handle an array's
   elements and a map's entries. Each carries its own `termination_by`; the
   measure `Doc.size` and its lemmas live at the end of `Doc.lean`.
6. **`inferCorpus` at `:269`** — the fold, plus where absence is counted.
7. **`toSchema` at `:287`** — hands off to the other half, and derives
   `parent` and `keyed` from each table's path.

Watch it run on a corpus:

```lean
#eval do
  let d ← IO.ofExcept (Doc.parse "[{\"a\":1},{\"a\":2.5},{}]")
  let ds ← IO.ofExcept (documents d |>.mapError Error.toString)
  let ts ← IO.ofExcept (inferCorpus {} ds |>.mapError Error.toString)
  for (p, t) in ts do
    IO.println s!"{Path.toString p}  visits={t.visits}"
    for (k, o) in t.members do
      IO.println s!"   {k} : {o.field.toString}  values={o.values} absent={o.absent}"
```

**Three comments in this file are worth reading as documentation, not
decoration:** the one on `TableObs` explaining why provenance is not observed,
the one on `observeObject` explaining what makes its termination *visible* to
Lean rather than merely true, and the one in `inferCorpus` explaining why
absence is counted at the end. Each records a decision that cost something to
get right.

## Step 5 — The other half: `Ocaml.lean` → `Gen.lean` → `Print.lean`

- **`Ocaml.lean`** (53 lines) — the output language, all of it. It cannot
  express a function body or any expression. That is deliberate; the docstring
  says why.
- **`Gen.lean:55`, `genModule`** — the design note's correspondence written as
  code. Read it beside §2.1 Step 4 of `tatami.pdf`; it is a line-by-line match.
- **`Gen.lean:32`, `moduleName`** — how paths become module names.
- **`Print.lean`** (51 lines) — deliberately dull. This is the step nothing can
  vouch for.

## Step 6 — The two supporting files

- **`Path.lean`** (72 lines) — `Seg` at `:4`, `Path` at `:15`. A path is a
  table's identity *and* the source of its module name. Small file,
  load-bearing.
- **`Mangle.lean:45`** — the escape scheme.

```lean
#eval mangle "my-field"   -- "my_2dfield"
#eval mangle "type"       -- "type_"
#eval mangle "Name"       -- "f_Name"
```

## Step 7 — Last: `Doc.lean`, `Config.lean`, `Error.lean`

Leave these until you understand the middle.

- **`Doc.lean`** — our JSON reader, plus the `Doc.size` measure the walk's
  termination rests on. The docstring at the top explains why we do not use
  `Lean.Json`; that is the interesting part. The parser is routine in what it
  does and dense in how it says it, because every branch carries its own proof
  that the input shrank.
- **`Config.lean`** — the markings. One option, `maps`, and one function
  inference calls, `isMap`.
- **`Error.lean`** — read it as a list. It is the complete answer to "what does
  this refuse", in 50 lines.

---

## If you only have an hour

`Main.lean:12` → `Ty.join` → `Ocaml.lean` → `Gen.genModule`. That is the
translation. Everything else is plumbing, accumulation, or wording.

## One warning

**One `partial` is left in the whole codebase**, `parseGo` in `Path.lean:56`,
which reads a path back from `.a.b[]`. A `partial` definition has no equations,
so Lean cannot reason about it at all. It blocks nothing currently stated —
paths come from the config file, which is a trusted boundary — but it is the
reason `Path.parse` cannot appear in a theorem.

Both of the ones that mattered are gone. `observeObject` is total on `Doc.size`,
so the three theorems in `Proofs/Inference.lean` have something to unfold; and
`pValue` is total on a subtype carrying the length decrease, which is why
`Doc.lean` is 464 lines rather than 140. Read the parser for what it does, not
for how it is written — the proofs are threaded through every branch and they
cost readability.

**One marking was removed.** There was a `recursive` config option folding a
path into an ancestor so both became one table. It is gone, and a config
naming it is rejected with a message saying so. Consequence worth holding on
to while you read: a table is identified by its path and by nothing else, so
`parent` and `keyed` are *computed* in `toSchema` rather than observed during
the walk.

---

## File sizes, for reference

| File | Lines | |
|---|---:|---|
| `Main.lean` | 90 | the pipeline, CLI, and `--json` report |
| `Tatami/Doc.lean` | 464 | the document type and JSON reader |
| `Tatami/Path.lean` | 72 | positions; a path identifies a table |
| `Tatami/Ty.lean` | 68 | types and the join |
| `Tatami/Config.lean` | 55 | the markings |
| `Tatami/Infer.lean` | 300 | the walk (four mutuals) and the accumulation |
| `Tatami/Schema.lean` | 28 | the handoff |
| `Tatami/Mangle.lean` | 87 | names |
| `Tatami/Ocaml.lean` | 86 | the output language |
| `Tatami/Gen.lean` | 135 | the correspondence, in code |
| `Tatami/Print.lean` | 51 | output language to text |
| `Tatami/Error.lean` | 53 | every rejection |
