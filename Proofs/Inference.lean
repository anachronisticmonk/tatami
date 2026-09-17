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

/-! ### Locality

`inferStep_countsFit` below needs to know that recursing into a member's own
subtree leaves the parent's table alone. `walk_frame` is that statement: the
walk changes no table whose path does not extend the one it started at. Since
a child's path extends its parent's strictly, the parent is then untouched.

Proved by `observeObject.induct`, one motive per mutually recursive function,
fifteen cases. -/

theorem except_bind_ok' {α β ε : Type} {x : Except ε α}
    {f : α → Except ε β} {r : β} (h : x >>= f = .ok r) :
    ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => injection h
  | ok a => exact ⟨a, rfl, h⟩

theorem lookup_map_ne {p q : Path} {f : TableObs → TableObs} (hne : q ≠ p) :
    ∀ ts : Tables,
      (ts.map (fun x => if x.1 == p then (x.1, f x.2) else x)).lookup q = ts.lookup q := by
  have hqp : (q == p) = false := by simpa using hne
  intro ts
  induction ts with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨a, t⟩ := hd
      simp only [beq_iff_eq] at ih
      simp only [List.map_cons, beq_iff_eq]
      by_cases hap : a = p
      · subst hap; simp [List.lookup_cons, hqp, ih]
      · simp [hap, List.lookup_cons, ih]

/-- `upsert` at `p` is invisible at every other path. -/
theorem upsert_lookup_ne {ts : Tables} {p q : Path} {f : TableObs → TableObs}
    (hne : q ≠ p) : (ts.upsert p f).lookup q = ts.lookup q := by
  unfold Tables.upsert
  split
  · exact lookup_map_ne hne ts
  · rw [List.lookup_append]
    cases h : ts.lookup q with
    | some v => simp
    | none => simp [hne]

/-- `ts'` differs from `ts` only at tables whose path extends `q`. -/
def Frame (q : Path) (ts ts' : Tables) : Prop :=
  ∀ r, ¬ (q <+: r) → ts'.lookup r = ts.lookup r

theorem frame_refl (q : Path) (ts : Tables) : Frame q ts ts := fun _ _ => rfl

theorem frame_trans {q : Path} {a b c : Tables}
    (h1 : Frame q a b) (h2 : Frame q b c) : Frame q a c :=
  fun r hr => (h2 r hr).trans (h1 r hr)

/-- A frame below a longer path is also a frame below any prefix of it. This is
    what turns "the child subtree was untouched outside itself" into "the
    parent's own row was untouched". -/
theorem frame_widen {q q' : Path} {a b : Tables}
    (hpre : q <+: q') (h : Frame q' a b) : Frame q a b :=
  fun r hr => h r (fun hq'r => hr (hpre.trans hq'r))

theorem frame_upsert {q p : Path} (hq : q <+: p) (ts : Tables)
    (f : TableObs → TableObs) : Frame q ts (ts.upsert p f) :=
  fun r hr => upsert_lookup_ne (fun hrp => hr (hrp ▸ hq))

theorem prefix_member (p : Path) (k : String) : p <+: p.member k := List.prefix_append ..
theorem prefix_elem (p : Path) : p <+: p.elem := List.prefix_append ..
theorem prefix_entry (p : Path) : p <+: p.entry := List.prefix_append ..

theorem recordMember_frame {ts ts' : Tables} {p q : Path} {k : String} {s : Seen}
    (hq : q <+: p) (h : recordMember ts p k s = .ok ts') : Frame q ts ts' := by
  unfold recordMember at h
  split at h
  · injection h with he; subst he; exact frame_upsert hq ts _
  · dsimp only at h
    split at h
    · injection h
    · injection h with he; subst he; exact frame_upsert hq ts _

theorem walk_frame (cfg : Config) (ts : Tables) (target : Path) (ic : Bool) (j : Doc) :
    ∀ ts', observeObject cfg ts target ic j = .ok ts' → Frame target ts ts' := by
  apply observeObject.induct cfg
    (motive1 := fun ts target ic j =>
      ∀ ts', observeObject cfg ts target ic j = .ok ts' → Frame target ts ts')
    (motive2 := fun ts target ms =>
      ∀ ts', observeMembers cfg ts target ms = .ok ts' → Frame target ts ts')
    (motive3 := fun ts et raw els =>
      ∀ ts', observeElems cfg ts et raw els = .ok ts' → Frame et ts ts')
    (motive4 := fun ts et raw es =>
      ∀ ts', observeEntries cfg ts et raw es = .ok ts' → Frame et ts ts')
  case case1 =>
    intro ts target ic ms ih2 ts' h
    rw [observeObject] at h
    obtain ⟨_, _, h⟩ := except_bind_ok' h
    exact frame_trans (frame_upsert (List.prefix_refl target) ts _) (ih2 ts' h)
  case case2 =>
    intro ts target ic other hno ts' h
    cases other <;> first
      | (rw [observeObject.eq_def] at h; injection h)
      | exact (hno _ rfl).elim
  case case3 =>
    intro ts target ts' h
    rw [observeMembers] at h
    injection h with he; subst he; exact frame_refl _ _
  case case4 =>
    intro ts target k tl here a hmap raw ih2 ih4 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    rw [if_pos hmap] at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hrest⟩ := except_bind_ok' hinner
    obtain ⟨_, _, hent⟩ := except_bind_ok' hrest
    have hpre : target <+: (target.member k).entry :=
      (prefix_member target k).trans (prefix_entry _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
      (frame_trans (frame_upsert hpre ts1 _)
        (frame_trans (frame_widen hpre (ih4 ts1 ts2 hent)) (ih2 ts2 ts' htl)))
  case case5 =>
    intro ts target k tl here a hmap ih2 ih1 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    rw [if_neg hmap] at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hobj⟩ := except_bind_ok' hinner
    exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
      (frame_trans (frame_widen (prefix_member target k) (ih1 ts1 ts2 hobj))
        (ih2 ts2 ts' htl))
  case case6 =>
    intro ts target k tl here els ih2 ih3 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hels⟩ := except_bind_ok' hinner
    have hpre : target <+: (target.member k).elem :=
      (prefix_member target k).trans (prefix_elem _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
      (frame_trans (frame_upsert hpre ts1 _)
        (frame_trans (frame_widen hpre (ih3 ts1 ts2 hels)) (ih2 ts2 ts' htl)))
  case case7 =>
    intro ts target k tl other hno1 hno2 ih2 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨_, _, hrec⟩ := except_bind_ok' hinner
         exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
           (ih2 ts1 ts' htl))
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim
  case case8 =>
    intro ts et raw ts' h
    rw [observeElems] at h
    injection h with he; subst he; exact frame_refl _ _
  case case9 =>
    intro ts et raw tl a _ ih3 ih1 ts' h
    rw [observeElems.eq_def] at h
    dsimp only at h
    obtain ⟨ts1, hobj, htl⟩ := except_bind_ok' h
    exact frame_trans (ih1 ts1 hobj) (ih3 ts1 ts' htl)
  case case10 =>
    intro ts et raw tl els _ ts' h
    rw [observeElems.eq_def] at h
    dsimp only at h
    injection h
  case case11 =>
    intro ts et raw tl other hno1 hno2 ih3 ts' h
    rw [observeElems.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨_, _, hrec⟩ := except_bind_ok' hinner
         exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
           (frame_trans (recordMember_frame (List.prefix_refl et) hrec)
             (ih3 ts1 ts' htl)))
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim
  case case12 =>
    intro ts et raw ts' h
    rw [observeEntries] at h
    injection h with he; subst he; exact frame_refl _ _
  case case13 =>
    intro ts et raw k tl a _ ih4 ih1 ts' h
    rw [observeEntries.eq_def] at h
    dsimp only at h
    obtain ⟨ts1, hobj, htl⟩ := except_bind_ok' h
    exact frame_trans (ih1 ts1 hobj) (ih4 ts1 ts' htl)
  case case14 =>
    intro ts et raw k tl els _ ts' h
    rw [observeEntries.eq_def] at h
    dsimp only at h
    injection h
  case case15 =>
    intro ts et raw k tl other hno1 hno2 ih4 ts' h
    rw [observeEntries.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨_, _, hrec⟩ := except_bind_ok' hinner
         exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
           (frame_trans (recordMember_frame (List.prefix_refl et) hrec)
             (ih4 ts1 ts' htl)))
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim


theorem walk_frame_members (cfg : Config) (ts : Tables) (target : Path)
    (ms : List (String × Doc)) :
    ∀ ts', observeMembers cfg ts target ms = .ok ts' → Frame target ts ts' := by
  apply observeMembers.induct cfg
    (motive1 := fun ts target ic j =>
      ∀ ts', observeObject cfg ts target ic j = .ok ts' → Frame target ts ts')
    (motive2 := fun ts target ms =>
      ∀ ts', observeMembers cfg ts target ms = .ok ts' → Frame target ts ts')
    (motive3 := fun ts et raw els =>
      ∀ ts', observeElems cfg ts et raw els = .ok ts' → Frame et ts ts')
    (motive4 := fun ts et raw es =>
      ∀ ts', observeEntries cfg ts et raw es = .ok ts' → Frame et ts ts')
  case case1 =>
    intro ts target ic ms ih2 ts' h
    rw [observeObject] at h
    obtain ⟨_, _, h⟩ := except_bind_ok' h
    exact frame_trans (frame_upsert (List.prefix_refl target) ts _) (ih2 ts' h)
  case case2 =>
    intro ts target ic other hno ts' h
    cases other <;> first
      | (rw [observeObject.eq_def] at h; injection h)
      | exact (hno _ rfl).elim
  case case3 =>
    intro ts target ts' h
    rw [observeMembers] at h
    injection h with he; subst he; exact frame_refl _ _
  case case4 =>
    intro ts target k tl here a hmap raw ih2 ih4 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    rw [if_pos hmap] at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hrest⟩ := except_bind_ok' hinner
    obtain ⟨_, _, hent⟩ := except_bind_ok' hrest
    have hpre : target <+: (target.member k).entry :=
      (prefix_member target k).trans (prefix_entry _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
      (frame_trans (frame_upsert hpre ts1 _)
        (frame_trans (frame_widen hpre (ih4 ts1 ts2 hent)) (ih2 ts2 ts' htl)))
  case case5 =>
    intro ts target k tl here a hmap ih2 ih1 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    rw [if_neg hmap] at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hobj⟩ := except_bind_ok' hinner
    exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
      (frame_trans (frame_widen (prefix_member target k) (ih1 ts1 ts2 hobj))
        (ih2 ts2 ts' htl))
  case case6 =>
    intro ts target k tl here els ih2 ih3 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hels⟩ := except_bind_ok' hinner
    have hpre : target <+: (target.member k).elem :=
      (prefix_member target k).trans (prefix_elem _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
      (frame_trans (frame_upsert hpre ts1 _)
        (frame_trans (frame_widen hpre (ih3 ts1 ts2 hels)) (ih2 ts2 ts' htl)))
  case case7 =>
    intro ts target k tl other hno1 hno2 ih2 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨_, _, hrec⟩ := except_bind_ok' hinner
         exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
           (ih2 ts1 ts' htl))
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim
  case case8 =>
    intro ts et raw ts' h
    rw [observeElems] at h
    injection h with he; subst he; exact frame_refl _ _
  case case9 =>
    intro ts et raw tl a _ ih3 ih1 ts' h
    rw [observeElems.eq_def] at h
    dsimp only at h
    obtain ⟨ts1, hobj, htl⟩ := except_bind_ok' h
    exact frame_trans (ih1 ts1 hobj) (ih3 ts1 ts' htl)
  case case10 =>
    intro ts et raw tl els _ ts' h
    rw [observeElems.eq_def] at h
    dsimp only at h
    injection h
  case case11 =>
    intro ts et raw tl other hno1 hno2 ih3 ts' h
    rw [observeElems.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨_, _, hrec⟩ := except_bind_ok' hinner
         exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
           (frame_trans (recordMember_frame (List.prefix_refl et) hrec)
             (ih3 ts1 ts' htl)))
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim
  case case12 =>
    intro ts et raw ts' h
    rw [observeEntries] at h
    injection h with he; subst he; exact frame_refl _ _
  case case13 =>
    intro ts et raw k tl a _ ih4 ih1 ts' h
    rw [observeEntries.eq_def] at h
    dsimp only at h
    obtain ⟨ts1, hobj, htl⟩ := except_bind_ok' h
    exact frame_trans (ih1 ts1 hobj) (ih4 ts1 ts' htl)
  case case14 =>
    intro ts et raw k tl els _ ts' h
    rw [observeEntries.eq_def] at h
    dsimp only at h
    injection h
  case case15 =>
    intro ts et raw k tl other hno1 hno2 ih4 ts' h
    rw [observeEntries.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨_, _, hrec⟩ := except_bind_ok' hinner
         exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
           (frame_trans (recordMember_frame (List.prefix_refl et) hrec)
             (ih4 ts1 ts' htl)))
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim

theorem walk_frame_elems (cfg : Config) (ts : Tables) (et : Path) (raw : String)
    (els : List Doc) :
    ∀ ts', observeElems cfg ts et raw els = .ok ts' → Frame et ts ts' := by
  apply observeElems.induct cfg
    (motive1 := fun ts target ic j =>
      ∀ ts', observeObject cfg ts target ic j = .ok ts' → Frame target ts ts')
    (motive2 := fun ts target ms =>
      ∀ ts', observeMembers cfg ts target ms = .ok ts' → Frame target ts ts')
    (motive3 := fun ts et raw els =>
      ∀ ts', observeElems cfg ts et raw els = .ok ts' → Frame et ts ts')
    (motive4 := fun ts et raw es =>
      ∀ ts', observeEntries cfg ts et raw es = .ok ts' → Frame et ts ts')
  case case1 =>
    intro ts target ic ms ih2 ts' h
    rw [observeObject] at h
    obtain ⟨_, _, h⟩ := except_bind_ok' h
    exact frame_trans (frame_upsert (List.prefix_refl target) ts _) (ih2 ts' h)
  case case2 =>
    intro ts target ic other hno ts' h
    cases other <;> first
      | (rw [observeObject.eq_def] at h; injection h)
      | exact (hno _ rfl).elim
  case case3 =>
    intro ts target ts' h
    rw [observeMembers] at h
    injection h with he; subst he; exact frame_refl _ _
  case case4 =>
    intro ts target k tl here a hmap raw ih2 ih4 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    rw [if_pos hmap] at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hrest⟩ := except_bind_ok' hinner
    obtain ⟨_, _, hent⟩ := except_bind_ok' hrest
    have hpre : target <+: (target.member k).entry :=
      (prefix_member target k).trans (prefix_entry _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
      (frame_trans (frame_upsert hpre ts1 _)
        (frame_trans (frame_widen hpre (ih4 ts1 ts2 hent)) (ih2 ts2 ts' htl)))
  case case5 =>
    intro ts target k tl here a hmap ih2 ih1 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    rw [if_neg hmap] at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hobj⟩ := except_bind_ok' hinner
    exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
      (frame_trans (frame_widen (prefix_member target k) (ih1 ts1 ts2 hobj))
        (ih2 ts2 ts' htl))
  case case6 =>
    intro ts target k tl here els ih2 ih3 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hels⟩ := except_bind_ok' hinner
    have hpre : target <+: (target.member k).elem :=
      (prefix_member target k).trans (prefix_elem _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
      (frame_trans (frame_upsert hpre ts1 _)
        (frame_trans (frame_widen hpre (ih3 ts1 ts2 hels)) (ih2 ts2 ts' htl)))
  case case7 =>
    intro ts target k tl other hno1 hno2 ih2 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨_, _, hrec⟩ := except_bind_ok' hinner
         exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
           (ih2 ts1 ts' htl))
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim
  case case8 =>
    intro ts et raw ts' h
    rw [observeElems] at h
    injection h with he; subst he; exact frame_refl _ _
  case case9 =>
    intro ts et raw tl a _ ih3 ih1 ts' h
    rw [observeElems.eq_def] at h
    dsimp only at h
    obtain ⟨ts1, hobj, htl⟩ := except_bind_ok' h
    exact frame_trans (ih1 ts1 hobj) (ih3 ts1 ts' htl)
  case case10 =>
    intro ts et raw tl els _ ts' h
    rw [observeElems.eq_def] at h
    dsimp only at h
    injection h
  case case11 =>
    intro ts et raw tl other hno1 hno2 ih3 ts' h
    rw [observeElems.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨_, _, hrec⟩ := except_bind_ok' hinner
         exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
           (frame_trans (recordMember_frame (List.prefix_refl et) hrec)
             (ih3 ts1 ts' htl)))
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim
  case case12 =>
    intro ts et raw ts' h
    rw [observeEntries] at h
    injection h with he; subst he; exact frame_refl _ _
  case case13 =>
    intro ts et raw k tl a _ ih4 ih1 ts' h
    rw [observeEntries.eq_def] at h
    dsimp only at h
    obtain ⟨ts1, hobj, htl⟩ := except_bind_ok' h
    exact frame_trans (ih1 ts1 hobj) (ih4 ts1 ts' htl)
  case case14 =>
    intro ts et raw k tl els _ ts' h
    rw [observeEntries.eq_def] at h
    dsimp only at h
    injection h
  case case15 =>
    intro ts et raw k tl other hno1 hno2 ih4 ts' h
    rw [observeEntries.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨_, _, hrec⟩ := except_bind_ok' hinner
         exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
           (frame_trans (recordMember_frame (List.prefix_refl et) hrec)
             (ih4 ts1 ts' htl)))
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim

theorem walk_frame_entries (cfg : Config) (ts : Tables) (et : Path) (raw : String)
    (es : List (String × Doc)) :
    ∀ ts', observeEntries cfg ts et raw es = .ok ts' → Frame et ts ts' := by
  apply observeEntries.induct cfg
    (motive1 := fun ts target ic j =>
      ∀ ts', observeObject cfg ts target ic j = .ok ts' → Frame target ts ts')
    (motive2 := fun ts target ms =>
      ∀ ts', observeMembers cfg ts target ms = .ok ts' → Frame target ts ts')
    (motive3 := fun ts et raw els =>
      ∀ ts', observeElems cfg ts et raw els = .ok ts' → Frame et ts ts')
    (motive4 := fun ts et raw es =>
      ∀ ts', observeEntries cfg ts et raw es = .ok ts' → Frame et ts ts')
  case case1 =>
    intro ts target ic ms ih2 ts' h
    rw [observeObject] at h
    obtain ⟨_, _, h⟩ := except_bind_ok' h
    exact frame_trans (frame_upsert (List.prefix_refl target) ts _) (ih2 ts' h)
  case case2 =>
    intro ts target ic other hno ts' h
    cases other <;> first
      | (rw [observeObject.eq_def] at h; injection h)
      | exact (hno _ rfl).elim
  case case3 =>
    intro ts target ts' h
    rw [observeMembers] at h
    injection h with he; subst he; exact frame_refl _ _
  case case4 =>
    intro ts target k tl here a hmap raw ih2 ih4 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    rw [if_pos hmap] at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hrest⟩ := except_bind_ok' hinner
    obtain ⟨_, _, hent⟩ := except_bind_ok' hrest
    have hpre : target <+: (target.member k).entry :=
      (prefix_member target k).trans (prefix_entry _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
      (frame_trans (frame_upsert hpre ts1 _)
        (frame_trans (frame_widen hpre (ih4 ts1 ts2 hent)) (ih2 ts2 ts' htl)))
  case case5 =>
    intro ts target k tl here a hmap ih2 ih1 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    rw [if_neg hmap] at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hobj⟩ := except_bind_ok' hinner
    exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
      (frame_trans (frame_widen (prefix_member target k) (ih1 ts1 ts2 hobj))
        (ih2 ts2 ts' htl))
  case case6 =>
    intro ts target k tl here els ih2 ih3 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hels⟩ := except_bind_ok' hinner
    have hpre : target <+: (target.member k).elem :=
      (prefix_member target k).trans (prefix_elem _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
      (frame_trans (frame_upsert hpre ts1 _)
        (frame_trans (frame_widen hpre (ih3 ts1 ts2 hels)) (ih2 ts2 ts' htl)))
  case case7 =>
    intro ts target k tl other hno1 hno2 ih2 ts' h
    rw [observeMembers.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨_, _, hrec⟩ := except_bind_ok' hinner
         exact frame_trans (recordMember_frame (List.prefix_refl target) hrec)
           (ih2 ts1 ts' htl))
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim
  case case8 =>
    intro ts et raw ts' h
    rw [observeElems] at h
    injection h with he; subst he; exact frame_refl _ _
  case case9 =>
    intro ts et raw tl a _ ih3 ih1 ts' h
    rw [observeElems.eq_def] at h
    dsimp only at h
    obtain ⟨ts1, hobj, htl⟩ := except_bind_ok' h
    exact frame_trans (ih1 ts1 hobj) (ih3 ts1 ts' htl)
  case case10 =>
    intro ts et raw tl els _ ts' h
    rw [observeElems.eq_def] at h
    dsimp only at h
    injection h
  case case11 =>
    intro ts et raw tl other hno1 hno2 ih3 ts' h
    rw [observeElems.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨_, _, hrec⟩ := except_bind_ok' hinner
         exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
           (frame_trans (recordMember_frame (List.prefix_refl et) hrec)
             (ih3 ts1 ts' htl)))
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim
  case case12 =>
    intro ts et raw ts' h
    rw [observeEntries] at h
    injection h with he; subst he; exact frame_refl _ _
  case case13 =>
    intro ts et raw k tl a _ ih4 ih1 ts' h
    rw [observeEntries.eq_def] at h
    dsimp only at h
    obtain ⟨ts1, hobj, htl⟩ := except_bind_ok' h
    exact frame_trans (ih1 ts1 hobj) (ih4 ts1 ts' htl)
  case case14 =>
    intro ts et raw k tl els _ ts' h
    rw [observeEntries.eq_def] at h
    dsimp only at h
    injection h
  case case15 =>
    intro ts et raw k tl other hno1 hno2 ih4 ts' h
    rw [observeEntries.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨_, _, hrec⟩ := except_bind_ok' hinner
         exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
           (frame_trans (recordMember_frame (List.prefix_refl et) hrec)
             (ih4 ts1 ts' htl)))
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim

/-! ### The counts add up

`inferFinish` computes `absent` as `visits - values - nulls` in `Nat`, where
subtraction truncates. So the identity `values + nulls + absent = visits` holds
exactly when `values + nulls ≤ visits`, and if that ever failed, a column a
document had omitted would report `absent = 0`, come out non-optional, and
`infer_admits` would be false rather than unproved.

That inequality is `CountsFit`. Everything below is proved except its
preservation by one document, which is `inferStep_countsFit`. -/

/-- Every column's recorded values and nulls fit inside its table's visit
    count. `visits` is incremented once per object seen at that path, and
    `recordMember` adds one to either `values` or `nulls` per member
    occurrence, so this is the statement that no member is recorded more times
    than its table was visited. -/
def CountsFit (ts : Tables) : Prop :=
  ∀ p t, (p, t) ∈ ts → ∀ k o, (k, o) ∈ t.members → o.values + o.nulls ≤ t.visits

theorem countsFit_nil : CountsFit [] := by intro p t hmem; simp at hmem

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {k : α} {v : β} :
    ∀ {l : List (α × β)}, l.lookup k = some v → (k, v) ∈ l := by
  intro l
  induction l with
  | nil => intro h; simp [List.lookup] at h
  | cons hd tl ih =>
      obtain ⟨a, b⟩ := hd
      intro h
      rw [List.lookup_cons] at h
      by_cases hk : k = a
      · subst hk
        simp at h
        subst h
        exact List.mem_cons_self ..
      · have : (k == a) = false := by simpa using hk
        rw [this] at h
        exact List.mem_cons_of_mem _ (ih h)

theorem mem_upsert {ts : Tables} {p q : Path} {f : TableObs → TableObs} {t' : TableObs}
    (h : (q, t') ∈ ts.upsert p f) :
    ((q, t') ∈ ts) ∨
      (q = p ∧ ∃ t0, t' = f t0 ∧
        ((p, t0) ∈ ts ∨ (t0 = {} ∧ ts.lookup p = none))) := by
  unfold Tables.upsert at h
  split at h
  · obtain ⟨⟨a, t0⟩, hmem, heq⟩ := List.mem_map.mp h
    dsimp only at heq
    split at heq
    · next hap =>
        injection heq with h1 h2
        have hap' : a = p := by simpa using hap
        exact Or.inr ⟨h1 ▸ hap', t0, h2.symm, Or.inl (hap' ▸ hmem)⟩
    · exact Or.inl (heq ▸ hmem)
  · next hs =>
      rcases List.mem_append.mp h with hl | hr
      · exact Or.inl hl
      · simp at hr
        obtain ⟨h1, h2⟩ := hr
        have hnone : ts.lookup p = none := by
          cases hl2 : ts.lookup p with
          | none => rfl
          | some v => rw [hl2] at hs; simp at hs
        exact Or.inr ⟨h1, {}, h2, Or.inr ⟨rfl, hnone⟩⟩



/-- With distinct paths, membership determines the lookup. -/
theorem lookup_of_mem_nodup {ts : Tables} {p : Path} {t : TableObs}
    (hnd : (ts.map Prod.fst).Nodup) (hmem : (p, t) ∈ ts) : ts.lookup p = some t := by
  induction ts with
  | nil => simp at hmem
  | cons hd tl ih =>
      obtain ⟨a, t0⟩ := hd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.lookup_cons]
      rcases List.mem_cons.mp hmem with heq | htl
      · injection heq with h1 h2
        subst h1; subst h2
        simp
      · have hne : p ≠ a := by
          intro hpa
          exact hnd.1 (hpa ▸ List.mem_map.mpr ⟨(p, t), htl, rfl⟩)
        have : (p == a) = false := by simpa using hne
        rw [this]
        exact ih hnd.2 htl

/-- Bumping a table's visit count cannot break the inequality. -/
theorem countsFit_upsert_visits {ts : Tables} {p : Path} {f : TableObs → TableObs}
    (hmem : ∀ t, (f t).members = t.members) (hvis : ∀ t, t.visits ≤ (f t).visits)
    (hfit : CountsFit ts) : CountsFit (ts.upsert p f) := by
  intro q t' hq k o hko
  rcases mem_upsert hq with hin | ⟨hqp, t0, ht', ht0⟩
  · exact hfit q t' hin k o hko
  · subst hqp; subst ht'
    rw [hmem t0] at hko
    rcases ht0 with hin0 | ⟨h0, _⟩
    · exact Nat.le_trans (hfit q t0 hin0 k o hko) (hvis t0)
    · subst h0; simp at hko



theorem recordMember_countsFit {ts ts' : Tables} {p : Path} {k : String} {s : Seen}
    {t : TableObs} (hnd : (ts.map Prod.fst).Nodup)
    (hlk : ts.lookup p = some t) (hvis : 1 ≤ t.visits)
    (hroom : ∀ o, t.members.lookup k = some o → o.values + o.nulls < t.visits)
    (hfit : CountsFit ts) (h : recordMember ts p k s = .ok ts') : CountsFit ts' := by
  have hcur : ((t.members.lookup k).getD ({} : Obs)).values
            + ((t.members.lookup k).getD ({} : Obs)).nulls + 1 ≤ t.visits := by
    cases hl : t.members.lookup k with
    | none => simp [hl]; omega
    | some o => have hr := hroom o hl; simp [hl]; omega
  have key : ∀ next : Obs, next.values + next.nulls ≤ t.visits →
      CountsFit (ts.upsert p (fun tt => { tt with
        members := tt.members.filter (fun q => q.1 != k) ++ [(k, next)] })) := by
    intro next hnext q t' hq k' o hko
    rcases mem_upsert hq with hin | ⟨hqp, t0, ht', ht0⟩
    · exact hfit q t' hin k' o hko
    · subst hqp; subst ht'
      have ht0t : t0 = t := by
        rcases ht0 with hin0 | ⟨_, hnone⟩
        · have hh := lookup_of_mem_nodup hnd hin0
          rw [hlk] at hh
          exact (Option.some_inj.mp hh.symm)
        · rw [hnone] at hlk; injection hlk
      subst ht0t
      dsimp only at hko
      rcases List.mem_append.mp hko with hf | hl
      · exact hfit _ t0 (lookup_mem hlk) k' o (List.mem_filter.mp hf).1
      · simp at hl
        obtain ⟨_, ho⟩ := hl
        subst ho
        exact hnext
  unfold recordMember at h
  simp only [hlk, Option.getD_some] at h
  split at h
  · injection h with he; subst he
    exact key _ (by simp; omega)
  · (try dsimp only at h)
    split at h
    · injection h
    · injection h with he; subst he
      exact key _ (by simp; omega)

theorem lookup_map_self {p : Path} {f : TableObs → TableObs} {t : TableObs} :
    ∀ ts : Tables, ts.lookup p = some t →
      (ts.map (fun x => if x.1 == p then (x.1, f x.2) else x)).lookup p = some (f t) := by
  intro ts
  induction ts with
  | nil => intro h; simp [List.lookup] at h
  | cons hd tl ih =>
      obtain ⟨a, b⟩ := hd
      intro h
      rw [List.lookup_cons] at h
      simp only [List.map_cons]
      by_cases hpa : p = a
      · subst hpa
        simp at h
        subst h
        simp [List.lookup_cons]
      · have hb : (p == a) = false := by simpa using hpa
        rw [hb] at h
        have hb2 : (a == p) = false := by simpa using (Ne.symm hpa)
        rw [if_neg (by simp [hb2])]
        rw [List.lookup_cons, hb]
        exact ih h

theorem upsert_lookup_self {ts : Tables} {p : Path} {f : TableObs → TableObs}
    {t : TableObs} (hlk : ts.lookup p = some t) :
    (ts.upsert p f).lookup p = some (f t) := by
  unfold Tables.upsert
  rw [if_pos (by rw [hlk]; rfl)]
  exact lookup_map_self ts hlk

theorem lookup_filter_ne {k k' : String} (hne : k' ≠ k) :
    ∀ l : List (String × Obs),
      (l.filter (fun q => q.1 != k)).lookup k' = l.lookup k' := by
  intro l
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨a, b⟩ := hd
      by_cases hak : a = k
      · subst hak
        have hk : (k' == a) = false := by simpa using hne
        simp [List.filter_cons, List.lookup_cons, hk, ih]
      · have hkeep : ((a, b).1 != k) = true := by simpa using hak
        simp only [List.filter_cons, hkeep, if_true, List.lookup_cons, ih]


theorem recordMember_lookup {ts ts' : Tables} {p : Path} {k : String} {s : Seen}
    {t : TableObs} (hlk : ts.lookup p = some t)
    (h : recordMember ts p k s = .ok ts') :
    ∃ t2, ts'.lookup p = some t2 ∧ t2.visits = t.visits ∧
      ∀ k', k' ≠ k → t2.members.lookup k' = t.members.lookup k' := by
  have body : ∀ next : Obs,
      ∃ t2, (ts.upsert p (fun tt => { tt with
          members := tt.members.filter (fun q => q.1 != k) ++ [(k, next)] })).lookup p = some t2
        ∧ t2.visits = t.visits
        ∧ ∀ k', k' ≠ k → t2.members.lookup k' = t.members.lookup k' := by
    intro next
    refine ⟨_, upsert_lookup_self hlk, rfl, ?_⟩
    intro k' hk'
    show (List.lookup k' (t.members.filter (fun q => q.1 != k) ++ [(k, next)])) = _
    rw [List.lookup_append, lookup_filter_ne hk']
    cases hl : t.members.lookup k' with
    | some v => simp
    | none => simp [hk']
  unfold recordMember at h
  simp only [hlk, Option.getD_some] at h
  split at h
  · injection h with he; subst he; exact body _
  · (try dsimp only at h)
    split at h
    · injection h
    · injection h with he; subst he; exact body _

theorem not_member_prefix (p : Path) (k : String) : ¬ (p.member k <+: p) := by
  intro h
  have hl := h.length_le
  simp [Path.member] at hl <;> omega

theorem not_elem_prefix (p : Path) : ¬ (p.elem <+: p) := by
  intro h
  have hl := h.length_le
  simp [Path.elem] at hl <;> omega

theorem not_entry_prefix (p : Path) : ¬ (p.entry <+: p) := by
  intro h
  have hl := h.length_le
  simp [Path.entry] at hl <;> omega

theorem upsert_lookup_self_none {ts : Tables} {p : Path} {f : TableObs → TableObs}
    (hlk : ts.lookup p = none) : (ts.upsert p f).lookup p = some (f {}) := by
  unfold Tables.upsert
  rw [if_neg (by rw [hlk]; simp)]
  rw [List.lookup_append, hlk]
  simp

theorem recordMember_nodup {ts ts' : Tables} {p : Path} {k : String} {s : Seen}
    (hnd : (ts.map Prod.fst).Nodup) (h : recordMember ts p k s = .ok ts') :
    (ts'.map Prod.fst).Nodup := by
  unfold recordMember at h
  split at h
  · injection h with he; subst he; exact upsert_nodup hnd
  · dsimp only at h
    split at h
    · injection h
    · injection h with he; subst he; exact upsert_nodup hnd

def Inv (ts : Tables) : Prop := CountsFit ts ∧ (ts.map Prod.fst).Nodup

/-- Every member still to be recorded at `p` has room for one more. -/
def Room (ts : Tables) (p : Path) (ks : List String) : Prop :=
  ∃ t, ts.lookup p = some t ∧ 1 ≤ t.visits ∧
    ∀ k ∈ ks, ∀ o, t.members.lookup k = some o → o.values + o.nulls < t.visits

theorem not_prefix_of_longer {p q : Path} (h : p.length < q.length) : ¬ (q <+: p) :=
  fun hpre => absurd hpre.length_le (by omega)

/-- Bumping the visit count restores room for every member. -/
theorem upsert_visit_room {ts : Tables} {p : Path} {f : TableObs → TableObs}
    (hmem : ∀ t, (f t).members = t.members) (hvis : ∀ t, (f t).visits = t.visits + 1)
    (hinv : Inv ts) (ks : List String) :
    Inv (ts.upsert p f) ∧ Room (ts.upsert p f) p ks := by
  refine ⟨⟨countsFit_upsert_visits hmem (fun t => by rw [hvis]; omega) hinv.1,
           upsert_nodup hinv.2⟩, ?_⟩
  cases hlk : ts.lookup p with
  | some t =>
      refine ⟨f t, upsert_lookup_self hlk, by rw [hvis]; omega, ?_⟩
      intro k _ o ho
      rw [hmem t] at ho
      have hb := hinv.1 p t (lookup_mem hlk) k o (lookup_mem ho)
      rw [hvis]; omega
  | none =>
      refine ⟨f {}, upsert_lookup_self_none hlk, by rw [hvis]; omega, ?_⟩
      intro k _ o ho
      rw [hmem {}] at ho
      simp at ho

theorem walk_inv (cfg : Config) (ts : Tables) (target : Path) (ic : Bool) (j : Doc) :
    ∀ ts', observeObject cfg ts target ic j = .ok ts' → Inv ts → Inv ts' := by
  apply observeObject.induct cfg
    (motive1 := fun ts target ic j =>
      ∀ ts', observeObject cfg ts target ic j = .ok ts' → Inv ts → Inv ts')
    (motive2 := fun ts target ms =>
      ∀ ts', observeMembers cfg ts target ms = .ok ts' → Inv ts →
        (ms.map Prod.fst).Nodup → Room ts target (ms.map Prod.fst) → Inv ts')
    (motive3 := fun ts et raw els =>
      ∀ ts', observeElems cfg ts et raw els = .ok ts' → Inv ts → Inv ts')
    (motive4 := fun ts et raw es =>
      ∀ ts', observeEntries cfg ts et raw es = .ok ts' → Inv ts → Inv ts')
  case case1 =>
    intro ts target ic ms ih2 ts' h hinv
    rw [observeObject] at h
    obtain ⟨u, hcd, h⟩ := except_bind_ok' h
    have hcd' : checkDistinct target ms = .ok () := hcd
    obtain ⟨hinv1, hroom⟩ :=
      upsert_visit_room (p := target)
        (f := fun t => { t with visits := t.visits + 1, elemObject := t.elemObject || ic })
        (fun _ => rfl) (fun _ => rfl) hinv (ms.map Prod.fst)
    exact ih2 ts' h hinv1 (checkDistinct_sound hcd') hroom
  case case2 =>
    intro ts target ic other hno ts' h hinv
    cases other <;> first
      | (rw [observeObject.eq_def] at h; injection h)
      | exact (hno _ rfl).elim
  case case3 =>
    intro ts target ts' h hinv _ _
    rw [observeMembers] at h
    injection h with he; subst he; exact hinv
  case case4 =>
    intro ts target k tl here a hmap raw ih2 ih4 ts' h hinv hndk hroom
    rw [observeMembers.eq_def] at h
    dsimp only at h
    rw [if_pos hmap] at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hrest⟩ := except_bind_ok' hinner
    obtain ⟨u, hcd, hent⟩ := except_bind_ok' hrest
    obtain ⟨t, hlk, hvis, hrm⟩ := hroom
    simp only [List.map_cons] at hndk
    have hsplit := List.nodup_cons.mp hndk
    have hinv1 : Inv ts1 :=
      ⟨recordMember_countsFit hinv.2 hlk hvis
         (fun o ho => hrm k (by simp) o ho) hinv.1 hrec,
       recordMember_nodup hinv.2 hrec⟩
    obtain ⟨t2, hlk2, hvis2, hmem2⟩ := recordMember_lookup hlk hrec
    have hneq : target ≠ ((target.member k).entry) := by
      intro hh
      have hl := congrArg List.length hh
      simp [Path.member, Path.entry] at hl
    have hinvU : Inv (ts1.upsert ((target.member k).entry) id) :=
      ⟨countsFit_upsert_visits (fun _ => rfl) (fun _ => Nat.le_refl _) hinv1.1,
       upsert_nodup hinv1.2⟩
    have hlkU : (ts1.upsert ((target.member k).entry) id).lookup target = some t2 :=
      (upsert_lookup_ne hneq).trans hlk2
    have hinv2 : Inv ts2 := ih4 ts1 ts2 hent hinvU
    have hnp : ¬ (((target.member k).entry) <+: target) :=
      not_prefix_of_longer (by simp [Path.member, Path.entry])
    have hlk3 : ts2.lookup target = some t2 :=
      (walk_frame_entries cfg (ts1.upsert ((target.member k).entry) id) ((target.member k).entry)
        (((target.member k).entry).toString) a ts2 hent target hnp).trans hlkU
    have hroom2 : Room ts2 target (tl.map Prod.fst) := by
      refine ⟨t2, hlk3, by rw [hvis2]; exact hvis, ?_⟩
      intro k' hk' o ho
      rw [hvis2]
      have hne : k' ≠ k := fun heq => hsplit.1 (heq ▸ hk')
      rw [hmem2 k' hne] at ho
      exact hrm k' (by simpa using List.mem_cons_of_mem k hk') o ho
    exact ih2 ts2 ts' htl hinv2 hsplit.2 hroom2
  case case5 =>
    intro ts target k tl here a hmap ih2 ih1 ts' h hinv hndk hroom
    rw [observeMembers.eq_def] at h
    dsimp only at h
    rw [if_neg hmap] at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hobj⟩ := except_bind_ok' hinner
    obtain ⟨t, hlk, hvis, hrm⟩ := hroom
    simp only [List.map_cons] at hndk
    have hsplit := List.nodup_cons.mp hndk
    have hinv1 : Inv ts1 :=
      ⟨recordMember_countsFit hinv.2 hlk hvis
         (fun o ho => hrm k (by simp) o ho) hinv.1 hrec,
       recordMember_nodup hinv.2 hrec⟩
    obtain ⟨t2, hlk2, hvis2, hmem2⟩ := recordMember_lookup hlk hrec
    have hinv2 : Inv ts2 := ih1 ts1 ts2 hobj hinv1
    have hnp : ¬ ((target.member k) <+: target) :=
      not_prefix_of_longer (by simp [Path.member])
    have hlk3 : ts2.lookup target = some t2 :=
      (walk_frame cfg ts1 (target.member k) false (Doc.obj a) ts2 hobj target hnp).trans hlk2
    have hroom2 : Room ts2 target (tl.map Prod.fst) := by
      refine ⟨t2, hlk3, by rw [hvis2]; exact hvis, ?_⟩
      intro k' hk' o ho
      rw [hvis2]
      have hne : k' ≠ k := fun heq => hsplit.1 (heq ▸ hk')
      rw [hmem2 k' hne] at ho
      exact hrm k' (by simpa using List.mem_cons_of_mem k hk') o ho
    exact ih2 ts2 ts' htl hinv2 hsplit.2 hroom2
  case case6 =>
    intro ts target k tl here els ih2 ih3 ts' h hinv hndk hroom
    rw [observeMembers.eq_def] at h
    dsimp only at h
    obtain ⟨ts2, hinner, htl⟩ := except_bind_ok' h
    obtain ⟨ts1, hrec, hels⟩ := except_bind_ok' hinner
    obtain ⟨t, hlk, hvis, hrm⟩ := hroom
    simp only [List.map_cons] at hndk
    have hsplit := List.nodup_cons.mp hndk
    have hinv1 : Inv ts1 :=
      ⟨recordMember_countsFit hinv.2 hlk hvis
         (fun o ho => hrm k (by simp) o ho) hinv.1 hrec,
       recordMember_nodup hinv.2 hrec⟩
    obtain ⟨t2, hlk2, hvis2, hmem2⟩ := recordMember_lookup hlk hrec
    have hneq : target ≠ ((target.member k).elem) := by
      intro hh
      have hl := congrArg List.length hh
      simp [Path.member, Path.elem] at hl
    have hinvU : Inv (ts1.upsert ((target.member k).elem) id) :=
      ⟨countsFit_upsert_visits (fun _ => rfl) (fun _ => Nat.le_refl _) hinv1.1,
       upsert_nodup hinv1.2⟩
    have hlkU : (ts1.upsert ((target.member k).elem) id).lookup target = some t2 :=
      (upsert_lookup_ne hneq).trans hlk2
    have hinv2 : Inv ts2 := ih3 ts1 ts2 hels hinvU
    have hnp : ¬ (((target.member k).elem) <+: target) :=
      not_prefix_of_longer (by simp [Path.member, Path.elem])
    have hlk3 : ts2.lookup target = some t2 :=
      (walk_frame_elems cfg (ts1.upsert ((target.member k).elem) id) ((target.member k).elem)
        (((target.member k).elem).toString) els ts2 hels target hnp).trans hlkU
    have hroom2 : Room ts2 target (tl.map Prod.fst) := by
      refine ⟨t2, hlk3, by rw [hvis2]; exact hvis, ?_⟩
      intro k' hk' o ho
      rw [hvis2]
      have hne : k' ≠ k := fun heq => hsplit.1 (heq ▸ hk')
      rw [hmem2 k' hne] at ho
      exact hrm k' (by simpa using List.mem_cons_of_mem k hk') o ho
    exact ih2 ts2 ts' htl hinv2 hsplit.2 hroom2
  case case7 =>
    intro ts target k tl other hno1 hno2 ih2 ts' h hinv hndk hroom
    rw [observeMembers.eq_def] at h
    dsimp only at h
    cases other
    case obj a => exact (hno1 a rfl).elim
    case arr e => exact (hno2 e rfl).elim
    all_goals
      (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
       obtain ⟨s, hsee, hrec⟩ := except_bind_ok' hinner
       obtain ⟨t, hlk, hvis, hrm⟩ := hroom
       simp only [List.map_cons] at hndk
       have hsplit := List.nodup_cons.mp hndk
       have hinv1 : Inv ts1 :=
         ⟨recordMember_countsFit hinv.2 hlk hvis
            (fun o ho => hrm k (by simp) o ho) hinv.1 hrec,
          recordMember_nodup hinv.2 hrec⟩
       obtain ⟨t2, hlk2, hvis2, hmem2⟩ := recordMember_lookup hlk hrec
       have hroom1 : Room ts1 target (tl.map Prod.fst) := by
         refine ⟨t2, hlk2, by rw [hvis2]; exact hvis, ?_⟩
         intro k' hk' o ho
         rw [hvis2]
         have hne : k' ≠ k := fun heq => hsplit.1 (heq ▸ hk')
         rw [hmem2 k' hne] at ho
         exact hrm k' (by simpa using List.mem_cons_of_mem k hk') o ho
       exact ih2 ts1 ts' htl hinv1 hsplit.2 hroom1)
  case case8 =>
    intro ts et raw ts' h hinv
    rw [observeElems] at h
    injection h with he; subst he; exact hinv
  case case9 =>
    intro ts et raw tl a _ ih3 ih1 ts' h hinv
    rw [observeElems.eq_def] at h
    dsimp only at h
    obtain ⟨ts1, hobj, htl⟩ := except_bind_ok' h
    exact ih3 ts1 ts' htl (ih1 ts1 hobj hinv)
  case case10 =>
    intro ts et raw tl els _ ts' h hinv
    rw [observeElems.eq_def] at h
    dsimp only at h
    injection h
  case case11 =>
    intro ts et raw tl other hno1 hno2 ih3 ts' h hinv
    rw [observeElems.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨s, hsee, hrec⟩ := except_bind_ok' hinner
         obtain ⟨hinvU, hroomU⟩ := upsert_visit_room (p := et)
           (f := fun t => { t with visits := t.visits + 1, elemScalar := true })
           (fun _ => rfl) (fun _ => rfl) hinv ["value"]
         obtain ⟨t, hlk, hvis, hrm⟩ := hroomU
         have hinv1 : Inv ts1 :=
           ⟨recordMember_countsFit hinvU.2 hlk hvis
              (fun o ho => hrm "value" (by simp) o ho) hinvU.1 hrec,
            recordMember_nodup hinvU.2 hrec⟩
         exact ih3 ts1 ts' htl hinv1)
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim
  case case12 =>
    intro ts et raw ts' h hinv
    rw [observeEntries] at h
    injection h with he; subst he; exact hinv
  case case13 =>
    intro ts et raw k tl a _ ih4 ih1 ts' h hinv
    rw [observeEntries.eq_def] at h
    dsimp only at h
    obtain ⟨ts1, hobj, htl⟩ := except_bind_ok' h
    exact ih4 ts1 ts' htl (ih1 ts1 hobj hinv)
  case case14 =>
    intro ts et raw k tl els _ ts' h hinv
    rw [observeEntries.eq_def] at h
    dsimp only at h
    injection h
  case case15 =>
    intro ts et raw k tl other hno1 hno2 ih4 ts' h hinv
    rw [observeEntries.eq_def] at h
    dsimp only at h
    cases other <;> first
      | (obtain ⟨ts1, hinner, htl⟩ := except_bind_ok' h
         obtain ⟨s, hsee, hrec⟩ := except_bind_ok' hinner
         obtain ⟨hinvU, hroomU⟩ := upsert_visit_room (p := et)
           (f := fun t => { t with visits := t.visits + 1, elemScalar := true })
           (fun _ => rfl) (fun _ => rfl) hinv ["value"]
         obtain ⟨t, hlk, hvis, hrm⟩ := hroomU
         have hinv1 : Inv ts1 :=
           ⟨recordMember_countsFit hinvU.2 hlk hvis
              (fun o ho => hrm "value" (by simp) o ho) hinvU.1 hrec,
            recordMember_nodup hinvU.2 hrec⟩
         exact ih4 ts1 ts' htl hinv1)
      | exact (hno1 _ rfl).elim
      | exact (hno2 _ rfl).elim


theorem inferStep_inv {cfg : Config} {ts ts' : Tables} {d : Doc}
    (hinv : Inv ts) (h : inferStep cfg ts d = .ok ts') : Inv ts' := by
  unfold inferStep at h
  exact walk_inv cfg ts [] false d ts' h hinv

private def stepLoop (cfg : Config) (d : Doc) (s : Tables) :
    Except Error (ForInStep Tables) := do
  let ts ← inferStep cfg s d
  pure (.yield ts)

/-- Folding the corpus preserves the inequality, one document at a time. -/
private theorem loop_inv (cfg : Config) :
    ∀ (ds : List Doc) (acc out : Tables),
      forIn ds acc (stepLoop cfg) = .ok out → Inv acc → Inv out := by
  intro ds
  induction ds with
  | nil =>
      intro acc out h hfit
      simp only [List.forIn_nil] at h
      injection h with he
      exact he ▸ hfit
  | cons d tl ih =>
      intro acc out h hfit
      simp only [List.forIn_cons, stepLoop, bind_assoc, pure_bind] at h
      obtain ⟨s1, h1, h2⟩ := except_bind_ok' h
      exact ih s1 out h2 (inferStep_inv hfit h1)

/-- Given the inequality, the final pass turns it into the identity. The two
    loops in `inferFinish` only reject, so the tables that come out are the
    tables that went in with `absent` filled in. -/
theorem inferFinish_counts {cfg : Config} {ts ts' : Tables}
    (h : inferFinish cfg ts = .ok ts') (hfit : CountsFit ts) :
    ∀ p t, (p, t) ∈ ts' → ∀ k o, (k, o) ∈ t.members →
      o.values + o.nulls + o.absent = t.visits := by
  unfold inferFinish at h
  obtain ⟨_, _, h⟩ := except_bind_ok' h
  obtain ⟨_, _, h⟩ := except_bind_ok' h
  injection h with hts
  subst hts
  intro p t hmem k o hko
  obtain ⟨⟨p0, t0⟩, hmem0, heq⟩ := List.mem_map.mp hmem
  injection heq with hp ht
  subst ht
  dsimp only at hko
  obtain ⟨⟨k0, o0⟩, hko0, heq0⟩ := List.mem_map.mp hko
  injection heq0 with hk ho
  subst ho
  have hle := hfit p0 t0 hmem0 k0 o0 hko0
  show o0.values + o0.nulls + (t0.visits - o0.values - o0.nulls) = t0.visits
  omega

/-- **Every column's counts add up to its table's visit count.**

    `inferFinish` computes `absent` by truncating subtraction, so without this
    a column a document had omitted could report `absent = 0`, come out
    non-optional, and make `infer_admits` false rather than merely unproved. -/
theorem infer_counts (cfg : Config) (ds : List Doc) (ts : Tables)
    (h : inferCorpus cfg ds = .ok ts) :
    ∀ p t, (p, t) ∈ ts → ∀ k o, (k, o) ∈ t.members →
      o.values + o.nulls + o.absent = t.visits := by
  unfold inferCorpus at h
  obtain ⟨mid, hloop, hfin⟩ := except_bind_ok' h
  exact inferFinish_counts hfin
    (loop_inv cfg ds [] mid hloop ⟨countsFit_nil, by simp⟩).1

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
