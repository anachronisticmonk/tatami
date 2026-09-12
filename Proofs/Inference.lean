import Tatami.Infer

/-!
# Inference

`Tatami.observeObject` is now total, so the statements below can be
approached: `observeObject.eq_def` exists, `unfold` works, and the recursion
has an induction principle. It was `partial` because the recursion is on a
member of an object rather than on the object, which is not structural; the
measure is `Doc.size`, and the four mutually recursive functions in
`Tatami.Infer` replace what were nested `for` loops, whose bodies gave the
termination checker nothing to attach to.

None of them is proved yet. `infer_perm` is a real claim and now has a route:
induction along the fold, using the join's commutativity, associativity and
idempotence from `Proofs.Lattice`. The other two need a specification before
they say anything at all.

The statements are written down now so that the shape of what is wanted is
fixed before the work starts.

Two of the three below conclude `True`, so they are reserved names rather than
unproved theorems: `trivial` would close them and nothing would be gained.
Saying what is wanted needs vocabulary that does not exist yet -- a relation
for "this document is described by this schema" -- and that relation has to be
written independently of `observeObject`, or the theorem restates the
implementation and proves nothing.

A third statement belongs here and is not yet written down: that for every
column `values + nulls + absent = visits`. `inferCorpus` computes `absent` by
truncating subtraction, so if that identity ever failed a column that should
be `option` would silently come out non-optional. It is a hypothesis of any
adequacy theorem, not bookkeeping for the report.
-/

namespace Tatami

/-- The schema is a property of the corpus, not of the order its documents
    arrived in. This is what makes "the schema" a meaningful phrase.

    **This statement has been wrong twice, and the second time it was the
    program that was wrong.**

    As an equation between `Tables` it is false, because `Tables` is a list.
    `Tables.upsert` appends a table when first seen, so the list records
    discovery order, and `recordMember` rebuilds a table's members as
    `filter (≠ k) ++ [k]`, so that list records order of last update:

        inferCorpus [{"x":{"p":1}}, {"y":{"q":1}}]  gives  [".", ".x", ".y"]
        inferCorpus [{"y":{"q":1}}, {"x":{"p":1}}]  gives  [".", ".y", ".x"]
        inferCorpus [{"a":1,"b":2}, {"a":3}]  gives members ["b", "a"]
        inferCorpus [{"a":3}, {"a":1,"b":2}]  gives members ["a", "b"]

    Neither reaches the output, since `toSchema` sorts, so the claim belongs
    on `toSchema`. It was false there too, for a separate reason: `parent` was
    observed, and it *overwrote* rather than merged, so a table reachable from
    two places kept whichever parent the last document happened to set.

    The `recursive` marking -- a path folded into an ancestor, so both became
    one table -- was the only way to produce such a table, and it has been
    removed. A table is identified by its path alone; its parent is
    `Path.parentOfElement` of that path and `keyed` is `Path.isEntry` of it,
    so neither is observed. Every field left in `TableObs` accumulates, which
    is exactly what the proof below needs.

    Conditional on success, because *which* error is reported first does
    depend on order -- if one document has a type conflict and another a
    nested array, the answer differs. Whether inference succeeds does not:
    every rejection is either symmetric (`join` is commutative, so a type
    conflict is a conflict either way), local to one document
    (`duplicateMember`, `nestedArray`), or checked at the end
    against accumulated flags (`mixedElements`, `markingMatchedNothing`).
    Diagnostics depending on order is fine; the schema depending on it is not.

    Not proved. Three things stand in the way, and the second and third are
    the interesting ones:

    * **The state is order-sensitive but the answer is not.** The proof needs
      an equivalence on `Tables` -- same tables, same columns, up to the order
      of both lists -- shown to be preserved by `observeObject` and to
      commute for two documents. Reasoning through the four mutually
      recursive functions for that is a large development.
    * **`toSchema` uses `Array.qsort`, which has no correctness lemmas in
      core** -- not even that it returns a permutation. So "the schema is a
      function of the multiset" is not currently statable. `List.mergeSort`
      has `mergeSort_perm`, but sortedness and the uniqueness of a sorted
      permutation both still need proving.
    * The cheaper route is to make order-independence **structural** rather
      than proved: observe each document from the empty state, then combine
      with a merge that is commutative and associative by construction --
      counts add, types join (`join_comm`, `join_assoc`, `join_idem`, all
      proved), flags disjoin, parents must agree. Permutation invariance then
      follows from `List.Perm` induction without touching the recursion. It
      changes where cross-document conflicts are detected, so it changes
      diagnostics, which is why it has not been done unilaterally. -/
theorem infer_perm (cfg : Config) (ds es : List Doc) (h : ds.Perm es)
    {ta tb : Tables} (hda : inferCorpus cfg ds = .ok ta)
    (hdb : inferCorpus cfg es = .ok tb) :
    toSchema ta = toSchema tb := by
  sorry

/-- The schema does not lie about the corpus: every value observed at a member
    fits the type that member was given. -/
theorem infer_admits (cfg : Config) (ds : List Doc) (ts : Tables)
    (h : inferCorpus cfg ds = .ok ts) :
    True := by
  sorry

/-- The type given to a member is the least one admitting every value observed
    there -- nothing is widened further than the data forces. Depends on
    `join_least`. -/
theorem infer_least (cfg : Config) (ds : List Doc) (ts : Tables)
    (h : inferCorpus cfg ds = .ok ts) :
    True := by
  sorry

end Tatami
