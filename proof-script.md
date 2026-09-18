# Tatami proof script

Two columns of instruction: **SCREEN** is what to have up, **SAY** is spoken
verbatim. Line breaks inside SAY are delivery beats, not sentence changes.

---

## 1 · Setup

**SCREEN** — nothing to open yet. Talking head, or hold the previous slide.

**SAY**

> Tatami infers a database schema from schemaless JSON. Why trust it?
>
> Because the OCaml signature we generate is a contract. And since we generate
> it rather than write it, we can prove things about the generator.
>
> It all comes down to one theorem.

---

## 2 · The theorem

**SCREEN** — open `Proofs/Correctness.lean`, scroll to **line 148**,
`theorem pipeline_correct`. Point at it.

**SAY**

> Here it is. If Tatami accepted your data and produced a schema, this
> guarantees five things.

*(beat — then one clause per finger, or per highlight)*

> One. The names it makes are always legal, and no two things end up with the
> same name.
>
> Two. Run it twice on the same data in a different order, and you get the exact
> same answer.
>
> Three. The shape comes through. If your JSON nests jobs inside runs, the
> generated code nests them the same way.
>
> Four. Every field gets the tightest type that still fits all the data.
>
> And five, a field is optional exactly when some record was missing it.

> That's the claim. Here's where it's proved.

---

## 3 · The twelve files

**SCREEN** — show the `Proofs/` folder in VS Code, file list visible.
Highlight each file as it is named.

**SAY**

> That's twelve files, and they're all about two questions. Is the schema right?
> And does the generated code say so?

| highlight | say |
|---|---|
| `Correctness.lean` | is the one we were just in, the five I've described. |
| `Counts.lean` | is the counting behind 'optional'. |
| `Inference.lean` | is where order stops mattering, and where the types come out as tight as they go. |
| `Lattice.lean` | proves joining two types is well defined in the first place. |
| `Mangle.lean` | is the renaming: a JSON field name becomes an OCaml one without two names ever turning into one. |
| `Merge.lean` | shows combining two documents works either way round. |
| `Tree.lean` | is the nesting surviving into the modules. |
| `Walk.lean` | keeps everything sorted as it reads. |
| `Wellformed.lean` | is the check behind number one. |

> And the rest prove the conditions those depend on.

*(the rest = `Order.lean`, `Sorted.lean`, `Spec.lean`)*

---

## 4 · It builds

**SCREEN** — terminal, the output of `lake build`.

**SAY**

> And it all builds. Two hundred and twenty-three theorems, and we have proved
> all of them in Lean4.

---

## Have ready before recording

- `Proofs/Correctness.lean` open at line 148, folded so `pipeline_correct` fills
  the frame
- VS Code explorer expanded on `Proofs/`, all twelve files visible without
  scrolling
- A terminal with `lake build` already run and its output on screen. Run it
  once beforehand so the take does not sit through a compile.

## Numbers used

| claim | where it comes from |
|---|---|
| five things | the five conjuncts of `pipeline_correct`, `Correctness.lean:148` |
| twelve files | `ls Proofs/*.lean` |
| 223 theorems | `theorem`/`lemma` declarations across `Proofs/`, counting the two that carry an attribute or modifier |
| all proved | zero `sorry` in `Proofs/` |
