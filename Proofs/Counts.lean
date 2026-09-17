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
  (ts.lookup p).isSome = true ∧
  ∀ t, (p, t) ∈ ts → 1 ≤ t.visits ∧
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
      (q = p ∧ ∃ t0, t' = f t0 ∧ ((p, t0) ∈ ts ∨ ts.lookup p = none)) := by
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
      · injection h2 with e1 e2; exact Or.inr ⟨e1, {}, e2, Or.inr hnone⟩
      · injection he with e1 e2; exact Or.inr ⟨e1, {}, e2, Or.inr hnone⟩



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

/-- Recording a member preserves the bound, given room for that member. -/
theorem recordMember_fits {ts : Tables} {p : Path} {k : String} {s : Seen}
    (hfit : CountsFit ts) (hroom : Room ts p [k]) :
    CountsFit (recordMember ts p k s) := by
  unfold recordMember
  intro q t' hq k' o hko
  rcases mem_upsert hq with hin | ⟨hqp, t0, ht', ht0⟩
  · exact hfit q t' hin k' o hko
  · subst hqp; subst ht'
    have ht0mem : (q, t0) ∈ ts := by
      rcases ht0 with hin0 | hnone
      · exact hin0
      · have hs := hroom.1; rw [hnone] at hs; simp at hs
    obtain ⟨hvis, hrm⟩ := hroom.2 t0 ht0mem
    have hone : ∀ ty b, ((⟨[ty], 1, 0, 0, b⟩ : Obs)).values + (⟨[ty], 1, 0, 0, b⟩ : Obs).nulls = 1 :=
      fun _ _ => rfl
    dsimp only at hko
    rcases mem_insertBy (fun _ _ hh => by simpa using hh) hko with h1 | h2 | ⟨o0, ho0, he⟩
    · exact hfit q t0 ht0mem k' o h1
    · cases h2
      cases s <;> (dsimp only; omega)
    · cases he
      have hr := hrm _ (by simp) o0 ho0
      cases s <;> (simp only [Obs.merge]; omega)

end Tatami
