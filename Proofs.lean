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

**Stated, not proved.**
* `join_least`, `join_assoc` --- the join is the *least* upper bound, and
  folding observations is order-independent.
* `mangle_injective` --- two distinct member names never give one identifier.
* `gen_wellFormed` --- every generated signature is well formed, which is what
  "the emitted code always compiles" amounts to.

**Blocked.**
* Everything about inference. `Tatami.observeObject` is `partial`, and a
  partial definition is opaque to proof. Making it total needs a size measure
  on `Doc` and the lemma that a member is smaller than the object holding it.

**Out of reach, and not for want of effort.**
* Anything about the data surviving. The program emits a description of
  tables and never emits a row, so there is no object for a preservation
  theorem to be about. That needs shredding first.
-/
