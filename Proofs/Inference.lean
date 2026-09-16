import Tatami.Infer
import Proofs.Spec

/-!
# Inference

`Tatami.observeObject` is now total, so the statements below can be
approached: `observeObject.eq_def` exists, `unfold` works, and the recursion
has an induction principle. It was `partial` because the recursion is on a
member of an object rather than on the object, which is not structural; the
measure is `Doc.size`, and the four mutually recursive functions in
`Tatami.Infer` replace what were nested `for` loops, whose bodies gave the
termination checker nothing to attach to.

**Proved.** `scalarTy_seeScalar` --- the specification and the implementation
agree on scalars. `ref_le` and `coll_le` --- widening a reference cannot
change which table it points at. `matchesField_mono` --- a value that matched
a field still matches it once later documents have widened that field. That
last one is the step adequacy turns on, and it is why `le_trans` exists in
`Proofs.Lattice`.

**Not proved.** The three theorems at the end, each `sorry` and each a real
claim. `infer_perm` has a route -- induction along the fold, using the join's
commutativity, associativity and idempotence from `Proofs.Lattice` -- but
three obstacles, set out in its own docstring. `infer_admits` and
`infer_least` are stated against `Conforms` and `Schema.le` from
`Proofs.Spec`, which is written independently of `observeObject`; that
independence is what stops them restating the implementation.

A fourth statement belongs here and is not yet written down: that for every
column `values + nulls + absent = visits`. `inferCorpus` computes `absent` by
truncating subtraction, so if that identity ever failed a column that should
be `option` would silently come out non-optional. It is a hypothesis of
`infer_admits`, not bookkeeping for the report.
-/

namespace Tatami

/-! ### The specification and the implementation agree on scalars

`scalarTy` in `Proofs.Spec` deliberately restates the rule in `seeScalar`
rather than calling it. This is the lemma that fails if the two ever drift
apart -- which is the whole point of writing the rule twice. -/

theorem scalarTy_seeScalar {p : String} {d : Doc} {ty : Ty} {b : Bool}
    (hs : d.isScalar = true) (h : seeScalar p d = .ok (.value ty b)) :
    scalarTy d = some ty := by
  cases d <;> simp_all [seeScalar, scalarTy, Doc.isScalar]
  -- the number case: both sides branch on the same conditions
  split at h
  · simp_all
  · split at h <;> (try split at h) <;> simp_all <;> omega

/-! ### Conformance survives widening

A reference only ever joins with a reference to the same table, so widening a
`ref` or `coll` field cannot change which table it points at. -/

theorem ref_le {q : Path} {t : Ty} (h : Ty.le (.ref q) t) : t = .ref q := by
  unfold Ty.le at h
  cases t <;> simp_all [Ty.join]

theorem coll_le {q : Path} {t : Ty} (h : Ty.le (.coll q) t) : t = .coll q := by
  unfold Ty.le at h
  cases t <;> simp_all [Ty.join]

/-- The lemma adequacy turns on: a value that matched a field still matches it
    after the field has been widened by later documents. Uses `le_trans`. -/
theorem matchesField_mono {s : Schema} {f g : Field} {v : Doc}
    (hty : Ty.le f.ty g.ty) (hn : f.nullable = true → g.nullable = true)
    (h : MatchesField s f v) : MatchesField s g v := by
  cases h with
  | null hf => exact .null (hn hf)
  | scalar hsc hle => exact .scalar hsc (le_trans hle hty)
  | @ref _ _ q hf hc =>
      rw [hf] at hty
      exact .ref (ref_le hty) hc
  | @arr _ _ q hf he hall =>
      rw [hf] at hty
      exact .arr (coll_le hty) he hall
  | @map _ _ q hf he hall =>
      rw [hf] at hty
      exact .map (coll_le hty) he hall

/-! ### The schema retains every table and column

The first thing `ConformsObj` asks for is the table sitting at a given path,
so adequacy cannot even begin until a table in `Tables` is known to survive
`toSchema`. Nothing could be said about that while `toSchema` sorted with
`Array.qsort`, which has no correctness lemmas in core -- not even that it
returns a permutation. `Array.mergeSort` has `mem_mergeSort`, and it holds of
*any* comparator, so neither lemma below needs the ordering to be sensible. -/

theorem mem_toSchema {ts : Tables} {p : Path} {t : TableObs} (h : (p, t) ∈ ts) :
    ({ path := p
     , parent := Path.parentOfElement p
     , keyed := Path.isEntry p
     , columns := (t.members.toArray.mergeSort (fun a b => a.1 < b.1)).toList.map
         fun (k, o) => { name := k, field := o.field } } : Table) ∈ toSchema ts := by
  unfold toSchema
  simp only [List.mem_map]
  exact ⟨(p, t), by simpa using h, rfl⟩

/-- A member observed at a table becomes a column of it, with the field the
    observation settled on. -/
theorem mem_columns_of_mem_members {t : TableObs} {k : String} {o : Obs}
    (h : (k, o) ∈ t.members) :
    ({ name := k, field := o.field } : Column) ∈
      (t.members.toArray.mergeSort (fun a b => a.1 < b.1)).toList.map
        (fun (k, o) => { name := k, field := o.field }) := by
  simp only [List.mem_map]
  exact ⟨(k, o), by simpa using h, rfl⟩

/-! ### A repeated member is refused

`checkDistinct` is the only thing standing between a document that binds one
member twice and a table that records it twice. The counts identity depends on
it -- `recordMember` touches each member once per visit only because a repeat
never reaches it. -/

theorem checkDistinct_go_sound (p : Path) :
    ∀ (ms : List (String × Doc)) (seen : List String),
      checkDistinct.go p seen ms = .ok () →
        (ms.map Prod.fst).Nodup ∧ ∀ k ∈ ms.map Prod.fst, k ∉ seen
  | [], _, _ => ⟨by simp, by simp⟩
  | (k, _) :: tl, seen, h => by
      simp only [checkDistinct.go] at h
      split at h
      · exact absurd h (by simp)
      · next hc =>
          obtain ⟨hnd, hns⟩ := checkDistinct_go_sound p tl (k :: seen) h
          have hk : k ∉ tl.map Prod.fst := fun hmem =>
            hns k hmem (List.mem_cons_self ..)
          refine ⟨?_, ?_⟩
          · simp only [List.map_cons]
            exact List.nodup_cons.mpr ⟨hk, hnd⟩
          · intro j hj
            simp only [List.map_cons] at hj
            rcases List.mem_cons.mp hj with rfl | hjt
            · simpa using hc
            · exact fun hseen => hns j hjt (List.mem_cons_of_mem _ hseen)

/-- Accepted by `checkDistinct` means the member names really are distinct. -/
theorem checkDistinct_sound {p : Path} {ms : List (String × Doc)}
    (h : checkDistinct p ms = .ok ()) : (ms.map Prod.fst).Nodup :=
  (checkDistinct_go_sound p ms [] h).1

/-! ### One table per path

`Tables` is an association list, so nothing in its type stops two entries
sharing a path. `upsert` is the only thing that extends it, and it appends
only when the path is absent. Without this, `mem_toSchema` gives a table at
the right path but not *the* table there, and `ConformsObj`, which asks for
`find?`, cannot use it. -/

/- `Seg` derives `BEq` but not `LawfulBEq`, and `List.lookup` compares with
   `==`, so relating "lookup found nothing" to "no key is this path" needs the
   instance. Every case of the derived comparison reduces definitionally; these
   name the reductions so `simp` can use them. -/
private theorem segBeq_mm (a b : String) :
    (Seg.member a == Seg.member b) = (a == b) := rfl
private theorem segBeq_me (a : String) : (Seg.member a == Seg.elem) = false := rfl
private theorem segBeq_mn (a : String) : (Seg.member a == Seg.entry) = false := rfl
private theorem segBeq_em (a : String) : ((Seg.elem : Seg) == Seg.member a) = false := rfl
private theorem segBeq_nm (a : String) : ((Seg.entry : Seg) == Seg.member a) = false := rfl
private theorem segBeq_en : ((Seg.elem : Seg) == Seg.entry) = false := rfl
private theorem segBeq_ne : ((Seg.entry : Seg) == Seg.elem) = false := rfl
private theorem segBeq_ee : ((Seg.elem : Seg) == Seg.elem) = true := rfl
private theorem segBeq_nn : ((Seg.entry : Seg) == Seg.entry) = true := rfl

instance : LawfulBEq Seg where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> simp_all [segBeq_mm, segBeq_me, segBeq_mn,
      segBeq_em, segBeq_nm, segBeq_en, segBeq_ne]
  rfl {a} := by cases a <;> simp [segBeq_mm, segBeq_ee, segBeq_nn]

theorem upsert_nodup {ts : Tables} {p : Path} {f : TableObs → TableObs}
    (h : (ts.map Prod.fst).Nodup) : ((ts.upsert p f).map Prod.fst).Nodup := by
  unfold Tables.upsert
  split
  · -- the path is already there: `map` rewrites values and leaves keys alone
    have hk : ∀ x : Path × TableObs,
        (Prod.fst ∘ fun (q, t) => if q == p then (q, f t) else (q, t)) x = Prod.fst x := by
      intro x; obtain ⟨q, t⟩ := x; simp only [Function.comp_apply]; split <;> rfl
    rw [List.map_map, List.map_congr_left (fun a _ => hk a)]
    exact h
  · -- the path is new, so appending it cannot repeat one
    next hn =>
      have hnone : ts.lookup p = none := by
        cases hl : ts.lookup p with
        | none => rfl
        | some _ => rw [hl] at hn; simp at hn
      have hnotin : p ∉ ts.map Prod.fst := by
        intro hmem
        obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
        have := (List.lookup_eq_none_iff.mp hnone) q hq
        rw [hqe] at this
        simp at this
      rw [List.map_append]
      refine List.nodup_append.mpr ⟨h, by simp, ?_⟩
      intro a ha b hb
      have : b = p := by simpa using hb
      subst this
      exact fun hab => hnotin (hab ▸ ha)

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

/-- **Adequacy.** The schema does not lie about the corpus: every document it
    was inferred from is described by it.

    This is the first statement in the project that mentions an input document
    and an output schema in the same breath. Everything else -- the lattice,
    the name theorems, well-formedness -- is a property of one stage in
    isolation, and a generator that ignored its input entirely would satisfy
    all of them.

    `Conforms` is defined in `Proofs.Spec`, independently of `observeObject`.
    That independence is what gives this theorem content.

    Not proved. The route is an induction mirroring `observeObject`'s own
    recursion, in three parts, of which the first two are done:

    * each value conforms at the moment it is recorded --- `recordMember`
      joins, and `le_join_right` gives the observation a place under the
      result;
    * conformance survives later widening --- `matchesField_mono`, above,
      which is why `le_trans` was needed;
    * a column's type only ever moves up as more documents arrive, which is
      the monotonicity invariant still to be established, and it has to hold
      of the whole `Tables` state at once.

    The nullability half needs the counts identity --- that
    `values + nulls + absent = visits` for every column, which is not yet
    stated. `inferCorpus` computes `absent` by truncating subtraction, so if
    that identity failed, a document that omitted a key would leave `absent`
    at zero, the column would come out non-optional, and this theorem would be
    false. -/
theorem infer_admits (cfg : Config) (ds : List Doc) (ts : Tables)
    (h : inferCorpus cfg ds = .ok ts) :
    Conforms (toSchema ts) ds := by
  sorry

/-- **Minimality.** The schema says no more than the data forces: any schema
    the whole corpus conforms to is above the inferred one.

    Adequacy alone is nearly free --- a corpus of integers is adequately
    described by `int`, by `int option`, and by `float`. This is what rules
    out the loose answers, and the two together pin the schema from both
    sides: adequacy forbids anything narrower, minimality anything wider.

    The table structure is assumed equal rather than compared, because it is
    forced by the shape of the documents, not chosen. Only the types and the
    nullability flags are up for comparison.

    Not proved. Rests on `join_least` (proved) lifted from two observations to
    a folded list, which needs `join_assoc` and `join_comm` (both proved), and
    on the same monotonicity invariant as adequacy. -/
theorem infer_least (cfg : Config) (ds : List Doc) (ts : Tables) (s : Schema)
    (h : inferCorpus cfg ds = .ok ts)
    (hstruct : s.map Table.path = (toSchema ts).map Table.path)
    (hconf : Conforms s ds) :
    Schema.le (toSchema ts) s := by
  sorry

end Tatami
