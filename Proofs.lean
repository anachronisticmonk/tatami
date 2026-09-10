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
* `mangle_injective` --- two distinct member names never give one identifier,
  so two members never become one column and two tables never one module.
  Three layers, each injective on the image of the one below: the byte
  encoding is prefix-free, so its concatenation is injective; no core can
  reach `f__`, so prefixed and unprefixed names stay disjoint; and no core
  ends in `_`, so a keyword with `_` appended is not a prefixed core.
* `mangle_starts_lower` --- a mangled name begins with a lowercase letter,
  which is what makes capitalising one character injective.
* `gen_wellFormed` --- every generated signature is well formed. Proved by
  inverting the check `gen` runs on its own output, so it holds of every
  `Schema` and does not need `mangle_injective`.

**Unblocked, not yet proved.**
* `Tatami.observeObject` is total now, on the measure `Doc.size`, so
  inference is reasonable about: it has equations and an induction principle.
  What was nested `for` loops is four mutually recursive functions.
* `infer_perm` is a real claim, and stating it correctly took two corrections.
  As an equation between `Tables` it is false, because that list carries
  discovery order and order of last update; and until `setParent` was added
  it was false even on `toSchema`, because `parent` overwrote rather than
  merged. It is now conditional on success, since which error is reported
  first legitimately depends on order while whether inference succeeds does
  not. Three obstacles remain, including that `Array.qsort` has no
  correctness lemmas in core -- see the docstring.
* `infer_admits` and `infer_least` conclude `True`. They are reserved names,
  not theorems, and totality does not change that: they need the conformance
  relation written first, independently of `observeObject`, or they restate
  the implementation.

**Not covered, though it sounds as if it were.**
* `File.WellFormed` constrains names only, not references. A `qualified M n`
  naming a module that does not exist, or one declared later in a file that
  is not `module rec`, satisfies it and still does not compile --- which is
  how the `recursive` fold bug slips past. "The emitted OCaml compiles" needs
  a scoping clause and `File.recursive` computed from every cross-module
  reference.

**Out of reach, and not for want of effort.**
* Anything about the data surviving. The program emits a description of
  tables and never emits a row, so there is no object for a preservation
  theorem to be about. That needs shredding first. Note also that a
  round-trip could only ever hold up to member order, explicit `null` versus
  an absent key, and the written form of a number --- all three are discarded
  by design --- and not at all for integers past `maxNativeInt`.
-/
