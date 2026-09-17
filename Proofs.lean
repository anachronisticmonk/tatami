import Proofs.Spec
import Proofs.Lattice
import Proofs.Mangle
import Proofs.Sorted
import Proofs.Order
import Proofs.Merge
import Proofs.Walk
import Proofs.Counts
import Proofs.Wellformed
import Proofs.Tree
import Proofs.Inference
import Proofs.Guarantees

/-!
# Proofs about the shredder

`Proofs.Guarantees` is the summary: `pipeline_correct`, in four named parts.
Everything below is what those parts rest on. There are no `sorry`s.

**The four guarantees** (`Proofs.Guarantees`).
* `signature_wellFormed` --- the emitted signature repeats no module name, no
  value name within a module, and no field name within a record.
* `schema_canonical` --- shuffle the corpus and the answer is *equal*, not
  merely equivalent, so two runs agree byte for byte.
* `structure_preserved` --- the tree the documents induce and the graph a
  reader finds in the signatures are the same graph: no edge lost, none
  invented, distinct tables to distinct modules, and rooted.
* `types_principal` --- each member gets the principal type of the values seen
  there: adequate (`infer_admits`) and least (`infer_least`).

**The type order** (`Proofs.Lattice`).
* `join_comm`, `join_idem`, `bot_le`, `le_join_left`, `le_join_right` --- the
  join sits above both arguments.
* `join_least`, `join_assoc` --- the join is the *least* upper bound, and
  folding is order-independent.
* `le_refl`, `le_antisymm`, `le_trans` --- it is a partial order. Transitivity
  falls out of `join_assoc`, and the fold in `Proofs.Inference` needs it at
  every step.

**Names** (`Proofs.Mangle`).
* `mangle_injective` --- two distinct member names never give one identifier,
  so two members never become one column and two tables never one module.
  Three layers, each injective on the image of the one below.
* `mangle_starts_lower` --- a mangled name begins with a lowercase letter,
  which is what makes capitalising one character injective.
* `mangleChars_not_keyword`, `mangle_not_keyword` --- a generated identifier is
  never an OCaml keyword. This does not follow from the other two: drop the
  keyword rule and both still hold while the generator emits
  `type t = { let : int }`, which OCaml rejects.

**Order-independence, structurally** (`Proofs.Sorted`, `Order`, `Merge`,
`Walk`). `Obs` holds the *set* of types seen rather than their running join,
each document is observed from nothing, and the results are merged. The merge
is commutative and associative in every field, and tables, members and type
sets are kept in order, so it is commutative *as a function*. `infer_perm` is
then an equality of `Tables`, proved from `foldl_perm_on` rather than by an
induction through the walk.

**The specification** (`Proofs.Spec`). Says, independently of the
implementation, when a document is *described by* a schema (`Conforms`) and
when one schema is *below* another (`Schema.le`). `scalarTy` there restates the
rule in `seeScalar` rather than calling it, and `scalarTy_seeScalar` is the
lemma that fails if the two drift apart --- it has already caught one drift,
when `seeScalar` gained a `uuid` case that `scalarTy` had not.

Nothing currently consumes `Conforms`: `infer_admits` and `infer_least` are
stated over `Obs.seen` and `Obs.joined` instead. Stating them over `Conforms`
as well would say what this file says at the level of documents rather than of
observations, and is the obvious next step.

**Not covered, though it sounds as if it were.**
* *Nullability.* Every theorem about types is silent about `option`.
  `inferFinish` computes `absent` as `visits - values - nulls` in `Nat`, where
  subtraction truncates, and nothing bounds `values + nulls` by `visits`. If
  that ever failed, a column a document omitted would report `absent = 0` and
  come out non-optional. It is the one obligation the restructure did not
  remove.
* *Null-only columns.* A member that only ever held `null` has an empty `seen`,
  so `joined` is `bot` and both halves of `types_principal` hold vacuously.
  There is no type information to constrain, but nothing constrains it.

**Out of reach, and not for want of effort.**
* Anything about the data surviving. The program emits a description of
  tables; the loader that fills them is OCaml, outside what Lean sees here. A
  preservation theorem needs the shredder first. Note also that a round-trip
  could only ever hold up to member order, explicit `null` versus an absent
  key, and the written form of a number --- all three are discarded by design
  --- and not at all for integers past `maxNativeInt`.
-/
