import Proofs.Walk

/-!
# The counts add up

`inferFinish` computes `absent` as `visits - values - nulls` in `Nat`, where
subtraction truncates. So `values + nulls + absent = visits` holds exactly
when `values + nulls ≤ visits`, and if that ever failed a column a document
had omitted would report `absent = 0` and come out non-optional.

That inequality is `CountsFit`. The merge preserves it because counts add on
both sides; the walk preserves it because `observeObject` counts the visit
before walking the members and `checkDistinct` stops a member being recorded
twice in one visit.
-/

namespace Tatami

example : LawfulBEq Path := inferInstance

/-- Every column's values and nulls fit inside its table's visit count. -/
def TableFits (t : TableObs) : Prop :=
  ∀ k o, (k, o) ∈ t.members → o.values + o.nulls ≤ t.visits

def CountsFit (ts : Tables) : Prop := ∀ p t, (p, t) ∈ ts → TableFits t

theorem countsFit_nil : CountsFit [] := by intro p t h; simp at h

/-- Every member still to be recorded at `p` has space for one more. -/
def Room (ts : Tables) (p : Path) (ks : List String) : Prop :=
  ∃ t, ts.lookup p = some t ∧ 1 ≤ t.visits ∧
    ∀ k ∈ ks, ∀ o, (k, o) ∈ t.members → o.values + o.nulls < t.visits

/-! ## Groundwork: what `upsert` does away from the path it writes -/

theorem insertBy_lookup_ne {lt eqk : K → K → Bool} {combine : V → V → V}
    [BEq K] [LawfulBEq K] (heqk : ∀ a b : K, eqk a b = true → a = b)
    {p q : K} {v : V} (hne : q ≠ p) :
    ∀ l : List (K × V), (insertBy lt eqk combine p v l).lookup q = l.lookup q := by
  have hqp : (q == p) = false := by simpa using hne
  intro l
  induction l with
  | nil => simp [insertBy, List.lookup_cons, hqp]
  | cons hd tl ih =>
      obtain ⟨k', v'⟩ := hd
      rw [insertBy]
      by_cases he : eqk p k' = true
      · rw [if_pos he]
        have hk : k' = p := (heqk p k' he).symm
        subst hk
        rw [List.lookup_cons, List.lookup_cons, hqp]
      · rw [if_neg he]
        by_cases hl : lt p k' = true
        · rw [if_pos hl, List.lookup_cons, hqp, List.lookup_cons]
        · rw [if_neg hl, List.lookup_cons, List.lookup_cons, ih]

theorem lookup_map_upd {p q : Path} {f : TableObs → TableObs} (hne : q ≠ p) :
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
  · exact lookup_map_upd hne ts
  · exact insertBy_lookup_ne (fun _ _ h => by simpa using h) hne ts



/-! ## Locality

The walk changes no table whose path does not extend the one it started at.
Recording a member at `target` is only safe if descending into that member's
own subtree left `target` alone, and since a child's path extends its
parent's strictly, that is what this gives. -/

def Frame (q : Path) (ts ts' : Tables) : Prop :=
  ∀ r, ¬ (q <+: r) → ts'.lookup r = ts.lookup r

theorem frame_refl (q : Path) (ts : Tables) : Frame q ts ts := fun _ _ => rfl

theorem frame_trans {q : Path} {a b c : Tables}
    (h1 : Frame q a b) (h2 : Frame q b c) : Frame q a c :=
  fun r hr => (h2 r hr).trans (h1 r hr)

theorem frame_widen {q q' : Path} {a b : Tables}
    (hpre : q <+: q') (h : Frame q' a b) : Frame q a b :=
  fun r hr => h r (fun hq'r => hr (hpre.trans hq'r))

theorem frame_upsert {q p : Path} (hq : q <+: p) (ts : Tables)
    (f : TableObs → TableObs) : Frame q ts (ts.upsert p f) :=
  fun r hr => upsert_lookup_ne (fun hrp => hr (hrp ▸ hq))

theorem recordMember_frame {q p : Path} (hq : q <+: p) (ts : Tables)
    (k : String) (s : Seen) : Frame q ts (recordMember ts p k s) := by
  unfold recordMember; exact frame_upsert hq ts _

theorem prefix_member (p : Path) (k : String) : p <+: p.member k := List.prefix_append ..
theorem prefix_elem (p : Path) : p <+: p.elem := List.prefix_append ..
theorem prefix_entry (p : Path) : p <+: p.entry := List.prefix_append ..

theorem not_prefix_of_longer {p q : Path} (h : p.length < q.length) : ¬ (q <+: p) :=
  fun hpre => absurd hpre.length_le (by omega)

theorem walk_frame (cfg : Config) :
    ∀ ts target inCollection j, ∀ ts',
      observeObject cfg ts target inCollection j = .ok ts' → Frame target ts ts' := by
  apply observeObject.induct cfg
    (motive1 := fun ts target inCollection j =>
      ∀ ts', observeObject cfg ts target inCollection j = .ok ts' → Frame target ts ts')
    (motive2 := fun ts target ms =>
      ∀ ts', observeMembers cfg ts target ms = .ok ts' → Frame target ts ts')
    (motive3 := fun ts et raw els =>
      ∀ ts', observeElems cfg ts et raw els = .ok ts' → Frame et ts ts')
    (motive4 := fun ts et raw es =>
      ∀ ts', observeEntries cfg ts et raw es = .ok ts' → Frame et ts ts')
  case case1 =>
    intro ts target inCollection ms ih ts' heq
    simp only [observeObject] at heq
    obtain ⟨_, _, h2⟩ := except_bind_ok heq
    exact frame_trans (frame_upsert (List.prefix_refl target) ts _) (ih ts' h2)
  case case2 =>
    intro ts target inCollection other hne ts' heq
    simp only [observeObject] at heq; cases heq
  case case3 =>
    intro ts target ts' heq
    simp only [observeMembers] at heq; cases heq; exact frame_refl _ _
  case case4 =>
    intro ts target k tl here a hmap raw ihtl ihentries ts' heq
    simp only [observeMembers] at heq
    rw [if_pos hmap] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hentries⟩ := except_bind_ok hin
    have hpre : target <+: (target.member k).entry :=
      (prefix_member target k).trans (prefix_entry _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) ts k _)
      (frame_trans (frame_upsert hpre _ _)
        (frame_trans (frame_widen hpre (ihentries ts1 hentries)) (ihtl ts1 ts' hrest)))
  case case5 =>
    intro ts target k tl here a hmap ihtl ihobj ts' heq
    simp only [observeMembers] at heq
    rw [if_neg hmap] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    exact frame_trans (recordMember_frame (List.prefix_refl target) ts k _)
      (frame_trans (frame_widen (prefix_member target k) (ihobj ts1 hin))
        (ihtl ts1 ts' hrest))
  case case6 =>
    intro ts target k tl here els ihtl ihelems ts' heq
    simp only [observeMembers] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    have hpre : target <+: (target.member k).elem :=
      (prefix_member target k).trans (prefix_elem _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) ts k _)
      (frame_trans (frame_upsert hpre _ _)
        (frame_trans (frame_widen hpre (ihelems ts1 hin)) (ihtl ts1 ts' hrest)))
  case case7 =>
    intro ts target k tl other hno1 hno2 ihtl ts' heq
    simp only [observeMembers] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    exact frame_trans (recordMember_frame (List.prefix_refl target) ts k _)
      (ihtl _ ts' hrest)
  case case8 =>
    intro ts et raw ts' heq
    simp only [observeElems] at heq; cases heq; exact frame_refl _ _
  case case9 =>
    intro ts et raw tl a _ ihtl ihobj ts' heq
    simp only [observeElems] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    exact frame_trans (ihobj ts1 hin) (ihtl ts1 ts' hrest)
  case case10 =>
    intro ts et raw tl els _ ts' heq
    simp only [observeElems] at heq
    obtain ⟨_, hin, _⟩ := except_bind_ok heq
    cases hin
  case case11 =>
    intro ts et raw tl other hno1 hno2 ihtl ts' heq
    simp only [observeElems] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
      (frame_trans (recordMember_frame (List.prefix_refl et) _ _ _) (ihtl _ ts' hrest))
  case case12 =>
    intro ts et raw ts' heq
    simp only [observeEntries] at heq; cases heq; exact frame_refl _ _
  case case13 =>
    intro ts et raw k tl a _ ihtl ihobj ts' heq
    simp only [observeEntries] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    exact frame_trans (ihobj ts1 hin) (ihtl ts1 ts' hrest)
  case case14 =>
    intro ts et raw k tl els ihtl ts' heq
    simp only [observeEntries] at heq
    obtain ⟨_, hin, _⟩ := except_bind_ok heq
    cases hin
  case case15 =>
    intro ts et raw k tl other hno1 hno2 ihtl ts' heq
    simp only [observeEntries] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
      (frame_trans (recordMember_frame (List.prefix_refl et) _ _ _) (ihtl _ ts' hrest))



theorem walk_frame_elems (cfg : Config) :
    ∀ ts et raw els, ∀ ts',
      observeElems cfg ts et raw els = .ok ts' → Frame et ts ts' := by
  apply observeElems.induct cfg
    (motive1 := fun ts target inCollection j =>
      ∀ ts', observeObject cfg ts target inCollection j = .ok ts' → Frame target ts ts')
    (motive2 := fun ts target ms =>
      ∀ ts', observeMembers cfg ts target ms = .ok ts' → Frame target ts ts')
    (motive3 := fun ts et raw els =>
      ∀ ts', observeElems cfg ts et raw els = .ok ts' → Frame et ts ts')
    (motive4 := fun ts et raw es =>
      ∀ ts', observeEntries cfg ts et raw es = .ok ts' → Frame et ts ts')
  case case1 =>
    intro ts target inCollection ms ih ts' heq
    simp only [observeObject] at heq
    obtain ⟨_, _, h2⟩ := except_bind_ok heq
    exact frame_trans (frame_upsert (List.prefix_refl target) ts _) (ih ts' h2)
  case case2 =>
    intro ts target inCollection other hne ts' heq
    simp only [observeObject] at heq; cases heq
  case case3 =>
    intro ts target ts' heq
    simp only [observeMembers] at heq; cases heq; exact frame_refl _ _
  case case4 =>
    intro ts target k tl here a hmap raw ihtl ihentries ts' heq
    simp only [observeMembers] at heq
    rw [if_pos hmap] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hentries⟩ := except_bind_ok hin
    have hpre : target <+: (target.member k).entry :=
      (prefix_member target k).trans (prefix_entry _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) ts k _)
      (frame_trans (frame_upsert hpre _ _)
        (frame_trans (frame_widen hpre (ihentries ts1 hentries)) (ihtl ts1 ts' hrest)))
  case case5 =>
    intro ts target k tl here a hmap ihtl ihobj ts' heq
    simp only [observeMembers] at heq
    rw [if_neg hmap] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    exact frame_trans (recordMember_frame (List.prefix_refl target) ts k _)
      (frame_trans (frame_widen (prefix_member target k) (ihobj ts1 hin))
        (ihtl ts1 ts' hrest))
  case case6 =>
    intro ts target k tl here els ihtl ihelems ts' heq
    simp only [observeMembers] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    have hpre : target <+: (target.member k).elem :=
      (prefix_member target k).trans (prefix_elem _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) ts k _)
      (frame_trans (frame_upsert hpre _ _)
        (frame_trans (frame_widen hpre (ihelems ts1 hin)) (ihtl ts1 ts' hrest)))
  case case7 =>
    intro ts target k tl other hno1 hno2 ihtl ts' heq
    simp only [observeMembers] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    exact frame_trans (recordMember_frame (List.prefix_refl target) ts k _)
      (ihtl _ ts' hrest)
  case case8 =>
    intro ts et raw ts' heq
    simp only [observeElems] at heq; cases heq; exact frame_refl _ _
  case case9 =>
    intro ts et raw tl a _ ihtl ihobj ts' heq
    simp only [observeElems] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    exact frame_trans (ihobj ts1 hin) (ihtl ts1 ts' hrest)
  case case10 =>
    intro ts et raw tl els _ ts' heq
    simp only [observeElems] at heq
    obtain ⟨_, hin, _⟩ := except_bind_ok heq
    cases hin
  case case11 =>
    intro ts et raw tl other hno1 hno2 ihtl ts' heq
    simp only [observeElems] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
      (frame_trans (recordMember_frame (List.prefix_refl et) _ _ _) (ihtl _ ts' hrest))
  case case12 =>
    intro ts et raw ts' heq
    simp only [observeEntries] at heq; cases heq; exact frame_refl _ _
  case case13 =>
    intro ts et raw k tl a _ ihtl ihobj ts' heq
    simp only [observeEntries] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    exact frame_trans (ihobj ts1 hin) (ihtl ts1 ts' hrest)
  case case14 =>
    intro ts et raw k tl els ihtl ts' heq
    simp only [observeEntries] at heq
    obtain ⟨_, hin, _⟩ := except_bind_ok heq
    cases hin
  case case15 =>
    intro ts et raw k tl other hno1 hno2 ihtl ts' heq
    simp only [observeEntries] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
      (frame_trans (recordMember_frame (List.prefix_refl et) _ _ _) (ihtl _ ts' hrest))

theorem walk_frame_entries (cfg : Config) :
    ∀ ts et raw es, ∀ ts',
      observeEntries cfg ts et raw es = .ok ts' → Frame et ts ts' := by
  apply observeEntries.induct cfg
    (motive1 := fun ts target inCollection j =>
      ∀ ts', observeObject cfg ts target inCollection j = .ok ts' → Frame target ts ts')
    (motive2 := fun ts target ms =>
      ∀ ts', observeMembers cfg ts target ms = .ok ts' → Frame target ts ts')
    (motive3 := fun ts et raw els =>
      ∀ ts', observeElems cfg ts et raw els = .ok ts' → Frame et ts ts')
    (motive4 := fun ts et raw es =>
      ∀ ts', observeEntries cfg ts et raw es = .ok ts' → Frame et ts ts')
  case case1 =>
    intro ts target inCollection ms ih ts' heq
    simp only [observeObject] at heq
    obtain ⟨_, _, h2⟩ := except_bind_ok heq
    exact frame_trans (frame_upsert (List.prefix_refl target) ts _) (ih ts' h2)
  case case2 =>
    intro ts target inCollection other hne ts' heq
    simp only [observeObject] at heq; cases heq
  case case3 =>
    intro ts target ts' heq
    simp only [observeMembers] at heq; cases heq; exact frame_refl _ _
  case case4 =>
    intro ts target k tl here a hmap raw ihtl ihentries ts' heq
    simp only [observeMembers] at heq
    rw [if_pos hmap] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hentries⟩ := except_bind_ok hin
    have hpre : target <+: (target.member k).entry :=
      (prefix_member target k).trans (prefix_entry _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) ts k _)
      (frame_trans (frame_upsert hpre _ _)
        (frame_trans (frame_widen hpre (ihentries ts1 hentries)) (ihtl ts1 ts' hrest)))
  case case5 =>
    intro ts target k tl here a hmap ihtl ihobj ts' heq
    simp only [observeMembers] at heq
    rw [if_neg hmap] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    exact frame_trans (recordMember_frame (List.prefix_refl target) ts k _)
      (frame_trans (frame_widen (prefix_member target k) (ihobj ts1 hin))
        (ihtl ts1 ts' hrest))
  case case6 =>
    intro ts target k tl here els ihtl ihelems ts' heq
    simp only [observeMembers] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    have hpre : target <+: (target.member k).elem :=
      (prefix_member target k).trans (prefix_elem _)
    exact frame_trans (recordMember_frame (List.prefix_refl target) ts k _)
      (frame_trans (frame_upsert hpre _ _)
        (frame_trans (frame_widen hpre (ihelems ts1 hin)) (ihtl ts1 ts' hrest)))
  case case7 =>
    intro ts target k tl other hno1 hno2 ihtl ts' heq
    simp only [observeMembers] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    exact frame_trans (recordMember_frame (List.prefix_refl target) ts k _)
      (ihtl _ ts' hrest)
  case case8 =>
    intro ts et raw ts' heq
    simp only [observeElems] at heq; cases heq; exact frame_refl _ _
  case case9 =>
    intro ts et raw tl a _ ihtl ihobj ts' heq
    simp only [observeElems] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    exact frame_trans (ihobj ts1 hin) (ihtl ts1 ts' hrest)
  case case10 =>
    intro ts et raw tl els _ ts' heq
    simp only [observeElems] at heq
    obtain ⟨_, hin, _⟩ := except_bind_ok heq
    cases hin
  case case11 =>
    intro ts et raw tl other hno1 hno2 ihtl ts' heq
    simp only [observeElems] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
      (frame_trans (recordMember_frame (List.prefix_refl et) _ _ _) (ihtl _ ts' hrest))
  case case12 =>
    intro ts et raw ts' heq
    simp only [observeEntries] at heq; cases heq; exact frame_refl _ _
  case case13 =>
    intro ts et raw k tl a _ ihtl ihobj ts' heq
    simp only [observeEntries] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    exact frame_trans (ihobj ts1 hin) (ihtl ts1 ts' hrest)
  case case14 =>
    intro ts et raw k tl els ihtl ts' heq
    simp only [observeEntries] at heq
    obtain ⟨_, hin, _⟩ := except_bind_ok heq
    cases hin
  case case15 =>
    intro ts et raw k tl other hno1 hno2 ihtl ts' heq
    simp only [observeEntries] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    exact frame_trans (frame_upsert (List.prefix_refl et) ts _)
      (frame_trans (recordMember_frame (List.prefix_refl et) _ _ _) (ihtl _ ts' hrest))

/-! ## What the two writes do to the counts -/

theorem mem_insertBy {lt eqk : K → K → Bool} {combine : V → V → V}
    (heqk : ∀ a b : K, eqk a b = true → a = b) {k : K} {v : V} :
    ∀ {l : List (K × V)} {pr : K × V}, pr ∈ insertBy lt eqk combine k v l →
      pr ∈ l ∨ pr = (k, v) ∨ ∃ o, (k, o) ∈ l ∧ pr = (k, combine o v) := by
  intro l
  induction l with
  | nil => intro pr h; rw [insertBy] at h; simp at h; exact Or.inr (Or.inl h)
  | cons hd tl ih =>
      intro pr h
      obtain ⟨k', v'⟩ := hd
      rw [insertBy] at h
      by_cases he : eqk k k' = true
      · rw [if_pos he] at h
        have hk : k = k' := heqk k k' he
        subst hk
        rcases List.mem_cons.mp h with rfl | ht
        · exact Or.inr (Or.inr ⟨v', List.mem_cons_self .., rfl⟩)
        · exact Or.inl (List.mem_cons_of_mem _ ht)
      · rw [if_neg he] at h
        by_cases hl : lt k k' = true
        · rw [if_pos hl] at h
          rcases List.mem_cons.mp h with rfl | ht
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl ht
        · rw [if_neg hl] at h
          rcases List.mem_cons.mp h with rfl | ht
          · exact Or.inl (List.mem_cons_self ..)
          · rcases ih ht with h1 | h2 | ⟨o, ho, he2⟩
            · exact Or.inl (List.mem_cons_of_mem _ h1)
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr ⟨o, List.mem_cons_of_mem _ ho, he2⟩)

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
      have hnone : ts.lookup p = none := by
        cases hl : ts.lookup p with
        | none => rfl
        | some _ => rw [hl] at hs; simp at hs
      rcases mem_insertBy (fun _ _ hh => by simpa using hh) h with h1 | h2 | ⟨o, ho, he⟩
      · exact Or.inl h1
      · injection h2 with e1 e2; exact Or.inr ⟨e1, {}, e2, Or.inr ⟨rfl, hnone⟩⟩
      · injection he with e1 e2; exact Or.inr ⟨e1, {}, e2, Or.inr ⟨rfl, hnone⟩⟩



theorem mem_lookup_isSome {ts : Tables} {p : Path} {t : TableObs}
    (h : (p, t) ∈ ts) : (ts.lookup p).isSome = true := by
  induction ts with
  | nil => simp at h
  | cons hd tl ih =>
      obtain ⟨a, t0⟩ := hd
      rw [List.lookup_cons]
      rcases List.mem_cons.mp h with he | ht
      · injection he with e1 _; subst e1; simp
      · by_cases hpa : (p == a) = true
        · rw [hpa]; simp
        · rw [Bool.not_eq_true] at hpa; rw [hpa]; exact ih ht

/-- With distinct keys, membership determines the lookup. -/
theorem lookup_of_mem_nodup {ts : Tables} {p : Path} {t : TableObs}
    (hnd : (ts.map Prod.fst).Nodup) (hmem : (p, t) ∈ ts) : ts.lookup p = some t := by
  induction ts with
  | nil => simp at hmem
  | cons hd tl ih =>
      obtain ⟨a, t0⟩ := hd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.lookup_cons]
      rcases List.mem_cons.mp hmem with heq | htl
      · injection heq with h1 h2; subst h1; subst h2; simp
      · have hne : p ≠ a := fun hpa =>
          hnd.1 (hpa ▸ List.mem_map.mpr ⟨(p, t), htl, rfl⟩)
        have : (p == a) = false := by simpa using hne
        rw [this]; exact ih hnd.2 htl

theorem tables_nodup {ts : Tables} (hok : TablesOk ts) : (ts.map Prod.fst).Nodup :=
  sortedBy_nodup pathOrder ts hok.1

/-- Recording a member preserves the bound, given room for that member. -/
theorem recordMember_fits {ts : Tables} {p : Path} {k : String} {s : Seen}
    (hok : TablesOk ts) (hfit : CountsFit ts) (hroom : Room ts p [k]) :
    CountsFit (recordMember ts p k s) := by
  obtain ⟨tp, hlk, hvis, hrm⟩ := hroom
  unfold recordMember
  intro q t' hq k' o hko
  rcases mem_upsert hq with hin | ⟨hqp, t0, ht', ht0⟩
  · exact hfit q t' hin k' o hko
  · subst hqp
    subst ht'
    have ht0mem : (q, t0) ∈ ts := by
      rcases ht0 with hin0 | hnone
      · exact hin0
      · rw [hnone.2] at hlk; injection hlk
    have ht0eq : t0 = tp := by
      have := lookup_of_mem_nodup (tables_nodup hok) ht0mem
      rw [hlk] at this
      exact (Option.some_inj.mp this).symm
    subst ht0eq
    dsimp only at hko
    rcases mem_insertBy (fun _ _ hh => by simpa using hh) hko with h1 | h2 | ⟨o0, ho0, he⟩
    · exact hfit q t0 ht0mem k' o h1
    · cases h2
      cases s <;> (dsimp only; omega)
    · cases he
      have hr := hrm _ (by simp) o0 ho0
      cases s <;> (simp only [Obs.merge]; omega)



/-! ## Reading back what was just written -/

theorem lookup_mem {K V : Type} [BEq K] [LawfulBEq K] {k : K} {v : V} :
    ∀ {l : List (K × V)}, l.lookup k = some v → (k, v) ∈ l := by
  intro l
  induction l with
  | nil => intro h; simp [List.lookup] at h
  | cons hd tl ih =>
      obtain ⟨a, b⟩ := hd
      intro h
      rw [List.lookup_cons] at h
      by_cases hk : k = a
      · subst hk; simp at h; subst h; exact List.mem_cons_self ..
      · have : (k == a) = false := by simpa using hk
        rw [this] at h
        exact List.mem_cons_of_mem _ (ih h)

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
        simp at h; subst h
        simp [List.lookup_cons]
      · have hb : (p == a) = false := by simpa using hpa
        rw [hb] at h
        have hb2 : (a == p) = false := by simpa using (Ne.symm hpa)
        rw [if_neg (by simp [hb2]), List.lookup_cons, hb]
        exact ih h

theorem upsert_lookup_self {ts : Tables} {p : Path} {f : TableObs → TableObs}
    {t : TableObs} (hlk : ts.lookup p = some t) :
    (ts.upsert p f).lookup p = some (f t) := by
  unfold Tables.upsert
  rw [if_pos (by rw [hlk]; rfl)]
  exact lookup_map_self ts hlk

theorem insertBy_lookup_self {lt eqk : K → K → Bool} [BEq K] [LawfulBEq K]
    (heqk : ∀ a b : K, eqk a b = true → a = b) {p : K} {v : V} :
    ∀ l : List (K × V), l.lookup p = none →
      (insertBy lt eqk (fun _ new => new) p v l).lookup p = some v := by
  intro l
  induction l with
  | nil => intro _; simp [insertBy, List.lookup_cons]
  | cons hd tl ih =>
      obtain ⟨k', v'⟩ := hd
      intro h
      rw [List.lookup_cons] at h
      by_cases hpk : (p == k') = true
      · rw [hpk] at h; simp at h
      · have hpk' : p ≠ k' := by simpa using hpk
        rw [Bool.not_eq_true] at hpk
        rw [hpk] at h
        rw [insertBy, if_neg (fun hc => hpk' (heqk p k' hc))]
        by_cases hl : lt p k' = true
        · rw [if_pos hl, List.lookup_cons]; simp
        · rw [if_neg hl, List.lookup_cons, hpk]; exact ih h

theorem upsert_lookup_self_none {ts : Tables} {p : Path} {f : TableObs → TableObs}
    (hlk : ts.lookup p = none) : (ts.upsert p f).lookup p = some (f {}) := by
  unfold Tables.upsert
  rw [if_neg (by rw [hlk]; simp)]
  exact insertBy_lookup_self (fun _ _ h => by simpa using h) ts hlk

/-! ## The two writes that are always safe -/

/-- A write that leaves `members` alone and does not lower `visits` cannot
    break the bound. Covers both the visit count and `upsert raw id`. -/
theorem upsert_fits_keep {ts : Tables} {p : Path} {f : TableObs → TableObs}
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

/-- Counting the visit restores room for every member of that table. -/
theorem upsert_visit_room {ts : Tables} {p : Path} {f : TableObs → TableObs}
    (hmem : ∀ t, (f t).members = t.members) (hvis : ∀ t, (f t).visits = t.visits + 1)
    (hfit : CountsFit ts) (ks : List String) : Room (ts.upsert p f) p ks := by
  cases hlk : ts.lookup p with
  | some t =>
      refine ⟨f t, upsert_lookup_self hlk, by rw [hvis]; omega, ?_⟩
      intro k _ o ho
      rw [hmem t] at ho
      have := hfit p t (lookup_mem hlk) k o ho
      rw [hvis]; omega
  | none =>
      refine ⟨f {}, upsert_lookup_self_none hlk, by rw [hvis]; omega, ?_⟩
      intro k _ o ho
      rw [hmem {}] at ho
      simp at ho


/-! ## A repeated member is refused, and what a record leaves behind -/

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

theorem checkDistinct_sound {p : Path} {ms : List (String × Doc)}
    (h : checkDistinct p ms = .ok ()) : (ms.map Prod.fst).Nodup :=
  (checkDistinct_go_sound p ms [] h).1

/-- Recording member `k` leaves the other members, and the visit count,
    exactly as they were -- so the room for them survives. -/
theorem recordMember_room {ts : Tables} {p : Path} {k : String} {s : Seen}
    {ks : List String} (hne : ∀ k' ∈ ks, k' ≠ k) (hroom : Room ts p (k :: ks)) :
    Room (recordMember ts p k s) p ks := by
  obtain ⟨t, hlk, hvis, hrm⟩ := hroom
  unfold recordMember
  refine ⟨_, upsert_lookup_self hlk, hvis, ?_⟩
  intro k' hk' o ho
  dsimp only at ho
  rcases mem_insertBy (fun _ _ hh => by simpa using hh) ho with h1 | h2 | ⟨o0, ho0, he⟩
  · exact hrm k' (List.mem_cons_of_mem _ hk') o h1
  · cases h2; exact absurd rfl (hne _ hk')
  · cases he; exact absurd rfl (hne _ hk')


/-! ## Carrying room across the other writes -/

theorem room_mono {ts : Tables} {p : Path} {ks ks' : List String}
    (hsub : ∀ k ∈ ks', k ∈ ks) (h : Room ts p ks) : Room ts p ks' :=
  let ⟨t, hlk, hv, hrm⟩ := h
  ⟨t, hlk, hv, fun k hk o ho => hrm k (hsub k hk) o ho⟩

/-- The child subtree was untouched outside itself, so the parent keeps its
    room. This is what `walk_frame` is for. -/
theorem room_frame {q p : Path} {ts ts' : Tables} {ks : List String}
    (hf : Frame q ts ts') (hnp : ¬ (q <+: p)) (h : Room ts p ks) : Room ts' p ks :=
  let ⟨t, hlk, hv, hrm⟩ := h
  ⟨t, (hf p hnp).trans hlk, hv, hrm⟩

theorem room_upsert_ne {ts : Tables} {p r : Path} {ks : List String}
    {f : TableObs → TableObs} (hne : p ≠ r) (h : Room ts p ks) :
    Room (ts.upsert r f) p ks :=
  let ⟨t, hlk, hv, hrm⟩ := h
  ⟨t, (upsert_lookup_ne hne).trans hlk, hv, hrm⟩

theorem ne_of_longer {p q : Path} (h : p.length < q.length) : p ≠ q :=
  fun he => by rw [he] at h; omega


/-! ## The walk keeps the counts in bounds

`observeObject` counts the visit before walking the members, which gives every
member of that table room for one more; `checkDistinct` stops any member being
recorded twice in that visit; and `walk_frame` carries the room across each
descent into a member's own subtree. -/

theorem walk_counts (cfg : Config) :
    ∀ ts target ic j, ∀ ts', observeObject cfg ts target ic j = .ok ts' →
      TablesOk ts → CountsFit ts → TablesOk ts' ∧ CountsFit ts' := by
  apply observeObject.induct cfg
    (motive1 := fun ts target ic j =>
      ∀ ts', observeObject cfg ts target ic j = .ok ts' →
        TablesOk ts → CountsFit ts → TablesOk ts' ∧ CountsFit ts')
    (motive2 := fun ts target ms =>
      ∀ ts', observeMembers cfg ts target ms = .ok ts' →
        TablesOk ts → CountsFit ts → (ms.map Prod.fst).Nodup →
        Room ts target (ms.map Prod.fst) → TablesOk ts' ∧ CountsFit ts')
    (motive3 := fun ts et raw els =>
      ∀ ts', observeElems cfg ts et raw els = .ok ts' →
        TablesOk ts → CountsFit ts → TablesOk ts' ∧ CountsFit ts')
    (motive4 := fun ts et raw es =>
      ∀ ts', observeEntries cfg ts et raw es = .ok ts' →
        TablesOk ts → CountsFit ts → TablesOk ts' ∧ CountsFit ts')
  case case1 =>
    intro ts target ic ms ih ts' heq hok hfit
    simp only [observeObject] at heq
    obtain ⟨u, hcd, h2⟩ := except_bind_ok heq
    exact ih ts' h2 (Tables.upsert_ok hok (fun _ ht => ht))
      (upsert_fits_keep (fun _ => rfl) (fun _ => Nat.le_succ _) hfit)
      (checkDistinct_sound (show checkDistinct target ms = .ok () from hcd))
      (upsert_visit_room (p := target)
        (f := fun t => { t with visits := t.visits + 1, elemObject := t.elemObject || ic })
        (fun _ => rfl) (fun _ => rfl) hfit (ms.map Prod.fst))
  case case2 =>
    intro ts target ic other hne ts' heq hok hfit
    simp only [observeObject] at heq; cases heq
  case case3 =>
    intro ts target ts' heq hok hfit _ _
    simp only [observeMembers] at heq; cases heq; exact ⟨hok, hfit⟩
  case case4 =>
    intro ts target k tl here a hmap raw ihtl ihentries ts' heq hok hfit hnd hroom
    simp only [observeMembers] at heq
    rw [if_pos hmap] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨u2, hcd2, hentries⟩ := except_bind_ok hin
    simp only [List.map_cons] at hnd
    have hsp := List.nodup_cons.mp hnd
    have hne : ∀ k' ∈ tl.map Prod.fst, k' ≠ k := fun k' hk' he => hsp.1 (he ▸ hk')
    have hokR := recordMember_ok (p := target) (k := k) (sn := Seen.value (Ty.coll raw) false) hok
    have hfitR := recordMember_fits (s := Seen.value (Ty.coll raw) false) hok hfit
      (room_mono (ks' := [k]) (by intro x hx; simp at hx; simp [hx]) hroom)
    have hroomR := recordMember_room (s := Seen.value (Ty.coll raw) false) hne hroom
    have hpre : target <+: (target.member k).entry :=
      (prefix_member target k).trans (prefix_entry _)
    have hlong : target.length < ((target.member k).entry).length := by
      simp [Path.member, Path.entry]
    have hokU := Tables.upsert_ok (p := raw) hokR (fun _ ht => ht)
    have hfitU := upsert_fits_keep (p := raw) (f := id) (fun _ => rfl) (fun _ => Nat.le_refl _) hfitR
    have hroomU := room_upsert_ne (f := id) (ne_of_longer hlong) hroomR
    obtain ⟨hok1, hfit1⟩ := ihentries ts1 hentries hokU hfitU
    have hroom1 := room_frame (walk_frame_entries cfg _ _ _ _ ts1 hentries)
      (not_prefix_of_longer hlong) hroomU
    exact ihtl ts1 ts' hrest hok1 hfit1 hsp.2 hroom1
  case case5 =>
    intro ts target k tl here a hmap ihtl ihobj ts' heq hok hfit hnd hroom
    simp only [observeMembers] at heq
    rw [if_neg hmap] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    simp only [List.map_cons] at hnd
    have hsp := List.nodup_cons.mp hnd
    have hne : ∀ k' ∈ tl.map Prod.fst, k' ≠ k := fun k' hk' he => hsp.1 (he ▸ hk')
    have hokR := recordMember_ok (p := target) (k := k) (sn := Seen.value (Ty.ref here) false) hok
    have hfitR := recordMember_fits (s := Seen.value (Ty.ref here) false) hok hfit
      (room_mono (ks' := [k]) (by intro x hx; simp at hx; simp [hx]) hroom)
    have hroomR := recordMember_room (s := Seen.value (Ty.ref here) false) hne hroom
    have hlong : target.length < (target.member k).length := by simp [Path.member]
    obtain ⟨hok1, hfit1⟩ := ihobj ts1 hin hokR hfitR
    have hroom1 := room_frame (walk_frame cfg _ _ _ _ ts1 hin)
      (not_prefix_of_longer hlong) hroomR
    exact ihtl ts1 ts' hrest hok1 hfit1 hsp.2 hroom1
  case case6 =>
    intro ts target k tl here els ihtl ihelems ts' heq hok hfit hnd hroom
    simp only [observeMembers] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    simp only [List.map_cons] at hnd
    have hsp := List.nodup_cons.mp hnd
    have hne : ∀ k' ∈ tl.map Prod.fst, k' ≠ k := fun k' hk' he => hsp.1 (he ▸ hk')
    have hokR := recordMember_ok (p := target) (k := k) (sn := Seen.value (Ty.coll (Path.elem here)) false) hok
    have hfitR := recordMember_fits (s := Seen.value (Ty.coll (Path.elem here)) false) hok hfit
      (room_mono (ks' := [k]) (by intro x hx; simp at hx; simp [hx]) hroom)
    have hroomR := recordMember_room (s := Seen.value (Ty.coll (Path.elem here)) false) hne hroom
    have hlong : target.length < ((target.member k).elem).length := by
      simp [Path.member, Path.elem]
    have hokU := Tables.upsert_ok (p := (Path.elem here)) hokR (fun _ ht => ht)
    have hfitU := upsert_fits_keep (p := (Path.elem here)) (f := id) (fun _ => rfl) (fun _ => Nat.le_refl _) hfitR
    have hroomU := room_upsert_ne (f := id) (ne_of_longer hlong) hroomR
    obtain ⟨hok1, hfit1⟩ := ihelems ts1 hin hokU hfitU
    have hroom1 := room_frame (walk_frame_elems cfg _ _ _ _ ts1 hin)
      (not_prefix_of_longer hlong) hroomU
    exact ihtl ts1 ts' hrest hok1 hfit1 hsp.2 hroom1
  case case7 =>
    intro ts target k tl other hno1 hno2 ihtl ts' heq hok hfit hnd hroom
    simp only [observeMembers] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    simp only [List.map_cons] at hnd
    have hsp := List.nodup_cons.mp hnd
    have hne : ∀ k' ∈ tl.map Prod.fst, k' ≠ k := fun k' hk' he => hsp.1 (he ▸ hk')
    exact ihtl _ ts' hrest (recordMember_ok hok)
      (recordMember_fits hok hfit (room_mono (ks' := [k]) (by intro x hx; simp at hx; simp [hx]) hroom))
      hsp.2 (recordMember_room hne hroom)
  case case8 =>
    intro ts et raw ts' heq hok hfit
    simp only [observeElems] at heq; cases heq; exact ⟨hok, hfit⟩
  case case9 =>
    intro ts et raw tl a _ ihtl ihobj ts' heq hok hfit
    simp only [observeElems] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨hok1, hfit1⟩ := ihobj ts1 hin hok hfit
    exact ihtl ts1 ts' hrest hok1 hfit1
  case case10 =>
    intro ts et raw tl els _ ts' heq hok hfit
    simp only [observeElems] at heq
    obtain ⟨_, hin, _⟩ := except_bind_ok heq
    cases hin
  case case11 =>
    intro ts et raw tl other hno1 hno2 ihtl ts' heq hok hfit
    simp only [observeElems] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    have hokU := Tables.upsert_ok (p := et)
      (f := fun t => { t with visits := t.visits + 1, elemScalar := true })
      hok (fun _ ht => ht)
    have hfitU := upsert_fits_keep (p := et)
      (f := fun t => { t with visits := t.visits + 1, elemScalar := true })
      (fun _ => rfl) (fun _ => Nat.le_succ _) hfit
    have hroomU := upsert_visit_room (p := et)
      (f := fun t => { t with visits := t.visits + 1, elemScalar := true })
      (fun _ => rfl) (fun _ => rfl) hfit ["value"]
    exact ihtl _ ts' hrest (recordMember_ok hokU)
      (recordMember_fits hokU hfitU (room_mono (by intro x hx; simp at hx; simp [hx]) hroomU))
  case case12 =>
    intro ts et raw ts' heq hok hfit
    simp only [observeEntries] at heq; cases heq; exact ⟨hok, hfit⟩
  case case13 =>
    intro ts et raw k tl a _ ihtl ihobj ts' heq hok hfit
    simp only [observeEntries] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨hok1, hfit1⟩ := ihobj ts1 hin hok hfit
    exact ihtl ts1 ts' hrest hok1 hfit1
  case case14 =>
    intro ts et raw k tl els ihtl ts' heq hok hfit
    simp only [observeEntries] at heq
    obtain ⟨_, hin, _⟩ := except_bind_ok heq
    cases hin
  case case15 =>
    intro ts et raw k tl other hno1 hno2 ihtl ts' heq hok hfit
    simp only [observeEntries] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    have hokU := Tables.upsert_ok (p := et)
      (f := fun t => { t with visits := t.visits + 1, elemScalar := true })
      hok (fun _ ht => ht)
    have hfitU := upsert_fits_keep (p := et)
      (f := fun t => { t with visits := t.visits + 1, elemScalar := true })
      (fun _ => rfl) (fun _ => Nat.le_succ _) hfit
    have hroomU := upsert_visit_room (p := et)
      (f := fun t => { t with visits := t.visits + 1, elemScalar := true })
      (fun _ => rfl) (fun _ => rfl) hfit ["value"]
    exact ihtl _ ts' hrest (recordMember_ok hokU)
      (recordMember_fits hokU hfitU (room_mono (by intro x hx; simp at hx; simp [hx]) hroomU))


/-! ## The merge keeps the bound, because counts add on both sides -/

theorem mem_mergeBy {K V : Type} (lt eqk : K → K → Bool) {combine : V → V → V}
    (heqk : ∀ a b : K, eqk a b = true → a = b) :
    ∀ a b : List (K × V), ∀ pr : K × V, pr ∈ mergeBy lt eqk combine a b →
      pr ∈ a ∨ pr ∈ b ∨
        ∃ ka va vb, (ka, va) ∈ a ∧ (ka, vb) ∈ b ∧ pr = (ka, combine va vb) := by
  apply mergeBy.induct lt eqk (motive := fun a b =>
    ∀ pr : K × V, pr ∈ mergeBy lt eqk combine a b →
      pr ∈ a ∨ pr ∈ b ∨
        ∃ ka va vb, (ka, va) ∈ a ∧ (ka, vb) ∈ b ∧ pr = (ka, combine va vb))
  · intro b pr h; rw [mergeBy] at h; exact Or.inr (Or.inl h)
  · intro a hne pr h
    cases a with
    | nil => exact (hne rfl).elim
    | cons x xs => simp only [mergeBy] at h; exact Or.inl h
  · intro ka va as kb vb bs he ih pr h
    have hkk : ka = kb := heqk ka kb he
    subst hkk
    rw [mergeBy, if_pos he] at h
    rcases List.mem_cons.mp h with rfl | ht
    · exact Or.inr (Or.inr ⟨ka, va, vb, List.mem_cons_self .., List.mem_cons_self .., rfl⟩)
    · rcases ih pr ht with h1 | h2 | ⟨k2, v1, v2, hv1, hv2, he2⟩
      · exact Or.inl (List.mem_cons_of_mem _ h1)
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h2))
      · exact Or.inr (Or.inr ⟨k2, v1, v2, List.mem_cons_of_mem _ hv1,
          List.mem_cons_of_mem _ hv2, he2⟩)
  · intro ka va as kb vb bs he hl ih pr h
    rw [mergeBy, if_neg he, if_pos hl] at h
    rcases List.mem_cons.mp h with rfl | ht
    · exact Or.inl (List.mem_cons_self ..)
    · rcases ih pr ht with h1 | h2 | ⟨k2, v1, v2, hv1, hv2, he2⟩
      · exact Or.inl (List.mem_cons_of_mem _ h1)
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨k2, v1, v2, List.mem_cons_of_mem _ hv1, hv2, he2⟩)
  · intro ka va as kb vb bs he hl ih pr h
    rw [mergeBy, if_neg he, if_neg hl] at h
    rcases List.mem_cons.mp h with rfl | ht
    · exact Or.inr (Or.inl (List.mem_cons_self ..))
    · rcases ih pr ht with h1 | h2 | ⟨k2, v1, v2, hv1, hv2, he2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h2))
      · exact Or.inr (Or.inr ⟨k2, v1, v2, hv1, List.mem_cons_of_mem _ hv2, he2⟩)

theorem tableObs_merge_fits {a b : TableObs} (ha : TableFits a) (hb : TableFits b) :
    TableFits (TableObs.merge a b) := by
  intro k o ho
  simp only [TableObs.merge] at ho ⊢
  rcases mem_mergeBy _ _ (fun _ _ hh => by simpa using hh) a.members b.members (k, o) ho with h1 | h2 | ⟨k2, v1, v2, hv1, hv2, he⟩
  · have := ha k o h1; omega
  · have := hb k o h2; omega
  · cases he
    have h1 := ha _ v1 hv1
    have h2 := hb _ v2 hv2
    simp only [Obs.merge]
    omega

theorem merge_countsFit {a b : Tables} (ha : CountsFit a) (hb : CountsFit b) :
    CountsFit (Tables.merge a b) := by
  intro p t hp k o hko
  simp only [Tables.merge] at hp
  rcases mem_mergeBy _ _ (fun _ _ hh => by simpa using hh) a b (p, t) hp with h1 | h2 | ⟨p2, t1, t2, ht1, ht2, he⟩
  · exact ha p t h1 k o hko
  · exact hb p t h2 k o hko
  · cases he
    exact tableObs_merge_fits (ha _ t1 ht1) (hb _ t2 ht2) k o hko


/-! ## The corpus, and the identity itself -/

theorem observeDocument_fits {cfg : Config} {d : Doc} {ts : Tables}
    (h : observeDocument cfg d = .ok ts) : CountsFit ts :=
  (walk_counts cfg [] [] false d ts h TablesOk.nil countsFit_nil).2

theorem fold_countsFit : ∀ l : List Tables, (∀ x, x ∈ l → CountsFit x) →
    ∀ b, CountsFit b → CountsFit (l.foldl Tables.merge b) := by
  intro l
  induction l with
  | nil => intro _ b hb; exact hb
  | cons x xs ih =>
      intro hall b hb
      exact ih (fun y hy => hall y (List.mem_cons_of_mem _ hy)) _
        (merge_countsFit hb (hall x (List.mem_cons_self ..)))

/-- Given the inequality, the final pass turns it into the identity. The three
    loops in `inferFinish` only reject, so the tables that come out are the
    tables that went in with `absent` filled in. -/
theorem inferFinish_counts {cfg : Config} {ts ts' : Tables}
    (h : inferFinish cfg ts = .ok ts') (hfit : CountsFit ts) :
    ∀ p t, (p, t) ∈ ts' → ∀ k o, (k, o) ∈ t.members →
      o.values + o.nulls + o.absent = t.visits := by
  unfold inferFinish at h
  obtain ⟨_, _, h1⟩ := except_bind_ok h
  obtain ⟨_, _, h2⟩ := except_bind_ok h1
  obtain ⟨_, _, h3⟩ := except_bind_ok h2
  injection h3 with hts
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
    non-optional, and make the nullability half of the schema wrong. -/
theorem infer_counts (cfg : Config) (ds : List Doc) (ts : Tables)
    (h : inferCorpus cfg ds = .ok ts) :
    ∀ p t, (p, t) ∈ ts → ∀ k o, (k, o) ∈ t.members →
      o.values + o.nulls + o.absent = t.visits := by
  unfold inferCorpus at h
  obtain ⟨tss, hm, hf⟩ := except_bind_ok h
  refine inferFinish_counts hf (fold_countsFit tss ?_ [] countsFit_nil)
  intro x hx
  obtain ⟨d, _, hd⟩ := mem_of_mapM_ok hm x hx
  exact observeDocument_fits hd

end Tatami