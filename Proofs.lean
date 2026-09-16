import Proofs.Spec
import Proofs.Layout
import Proofs.Lattice
import Proofs.Mangle
import Proofs.Wellformed
import Proofs.Inference

/-!
# Proofs about the shredder

What is stated here, and where each stands.

**Proved.**
* `join_comm`, `join_idem`, `bot_le`, `le_join_left`, `le_join_right` --- the
  type order is a genuine order and the join sits above both arguments.
* `join_least`, `join_assoc` --- the join is the *least* upper bound, and
  folding observations is order-independent. Together with the above, an
  inferred type is the tightest one the data admits.
* `le_refl`, `le_antisymm`, `le_trans` --- the type order is a partial order.
  Transitivity falls out of `join_assoc`.
* `mangle_injective` --- two distinct member names never give one identifier,
  so two members never become one column and two tables never one module.
  Three layers, each injective on the image of the one below: the byte
  encoding is prefix-free, so its concatenation is injective; no core can
  reach `f__`, so prefixed and unprefixed names stay disjoint; and no core
  ends in `_`, so a keyword with `_` appended is not a prefixed core.
* `mangle_starts_lower` --- a mangled name begins with a lowercase letter,
  which is what makes capitalising one character injective.
* `mangleChars_not_keyword`, `mangle_not_keyword` --- a generated identifier
  is never an OCaml keyword. With `mangle_starts_lower` this is what "legal
  identifier" amounts to for this fragment. Neither follows from injectivity:
  drop the keyword rule and injectivity and the lowercase-start property both
  stay true while the generator emits `type t = { let : int }`, which OCaml
  rejects.
* `gen_wellFormed` --- every generated signature is well formed. Proved by
  inverting the check `gen` runs on its own output, so it holds of every
  `Schema` and does not need `mangle_injective`.
* `scalarTy_seeScalar` --- specification and implementation agree on scalars.
* `ref_le`, `coll_le` --- a reference only widens to a reference to the same
  table.
* `matchesField_mono` --- a value that matched a field still matches it after
  later documents widen that field. This is the step adequacy turns on.
* `mem_layoutOf` --- every member becomes a column, under its mangled name, at
  the type inference gave it, optional exactly when the member was ever
  missing or null. The design note's first correspondence, with the two
  exceptions the implementation makes and the prose does not state: a member
  named `id` is consumed as the key, and a member holding a collection
  contributes no column, since the elements carry the key back instead.

**The specification.**
* `Proofs.Spec` says, independently of the implementation, when a document is
  *described by* a schema (`Conforms`) and when one schema is *below* another
  (`Schema.le`). Without it, `inferCorpus` is the only account of a schema the
  project has, and "correct" means "whatever that produces". `scalarTy` there
  restates the rule in `seeScalar` rather than calling it; `scalarTy_seeScalar`
  is the lemma that fails if the two drift apart, and it has already caught
  one drift --- `seeScalar` gained a `uuid` case that `scalarTy` had not.

**Unblocked, not yet proved.**
* `Tatami.observeObject` is total now, on the measure `Doc.size`, so
  inference is reasonable about: it has equations and an induction principle.
  What was nested `for` loops is four mutually recursive functions.
* `infer_perm` is a real claim, and stating it correctly took two corrections.
  As an equation between `Tables` it is false, because that list carries
  discovery order and order of last update; and it was false on `toSchema`
  too while `parent` was observed, because it overwrote rather than merged.
  Removing the `recursive` marking removed the only way to reach one table
  from two places, so parent and `keyed` are read off the path and nothing
  left in `TableObs` overwrites. It is now conditional on success, since
  which error is reported first legitimately depends on order while whether
  inference succeeds does not. Three obstacles remain, including that `Array.qsort` has no
  correctness lemmas in core -- see the docstring.
* `infer_admits` and `infer_least` are now stated against `Conforms` and
  `Schema.le`, so they are real claims rather than the reserved names they
  used to be. Both rest on a monotonicity invariant --- that a column's type
  only ever moves up as documents arrive --- which has to hold of the whole
  `Tables` state at once and is not yet established. Adequacy additionally
  needs the counts identity, which is not yet stated.

**Not covered, though it sounds as if it were.**
* `File.WellFormed` constrains names only, not references. A `qualified M n`
  naming a module that does not exist, or one that is compiled *after* the
  unit naming it, satisfies this definition and still does not compile. Each
  module is now its own `.mli`, so the ordering obligation is real and
  external: `File.units` emits `Ids` first and the rest deepest-first, and
  nothing states that this order is a topological sort of the references.
  "The emitted OCaml compiles" needs that, plus a scoping clause.

**Out of reach, and not for want of effort.**
* Anything about the data surviving. The program emits a description of
  tables and never emits a row, so there is no object for a preservation
  theorem to be about. That needs shredding first. Note also that a
  round-trip could only ever hold up to member order, explicit `null` versus
  an absent key, and the written form of a number --- all three are discarded
  by design --- and not at all for integers past `maxNativeInt`.
-/
