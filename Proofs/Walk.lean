import Proofs.Merge

/-!
# The walk keeps its observations in order

`Proofs.Merge` proves `Tables.merge` commutative and associative *given*
`TablesOk` -- every list in key order. This discharges that hypothesis for
everything inference builds: the walk touches `Tables` only through `upsert`
and `recordMember`, both of which preserve the order.

The induction is Lean's own `observeObject.induct`, which carries one motive
per function of the mutual block, so the four walk functions are handled
together on the measure they were defined by.
-/

namespace Tatami

/-- Each of the three record updates the walk makes leaves `members` alone,
    so each preserves the invariant. -/
private theorem keep {f : TableObs → TableObs}
    (hm : ∀ t, (f t).members = t.members) : ∀ t, TableObsOk t → TableObsOk (f t) := by
  intro t ht
  exact ⟨by rw [hm t]; exact ht.1, by rw [hm t]; exact ht.2⟩

theorem observe_ok (cfg : Config) :
    ∀ ts target inCollection j, TablesOk ts → ∀ ts',
      observeObject cfg ts target inCollection j = .ok ts' → TablesOk ts' := by
  apply observeObject.induct cfg
    (motive1 := fun ts target inCollection j =>
      TablesOk ts → ∀ ts', observeObject cfg ts target inCollection j = .ok ts' → TablesOk ts')
    (motive2 := fun ts target ms =>
      TablesOk ts → ∀ ts', observeMembers cfg ts target ms = .ok ts' → TablesOk ts')
    (motive3 := fun ts elemTable raw els =>
      TablesOk ts → ∀ ts', observeElems cfg ts elemTable raw els = .ok ts' → TablesOk ts')
    (motive4 := fun ts entryTable raw es =>
      TablesOk ts → ∀ ts', observeEntries cfg ts entryTable raw es = .ok ts' → TablesOk ts')
  -- observeObject, an object: count the visit, then walk the members
  case case1 =>
    intro ts target inCollection ms ih h ts' heq
    simp only [observeObject] at heq
    obtain ⟨_, _, h2⟩ := except_bind_ok heq
    exact ih (Tables.upsert_ok h (keep (fun _ => rfl))) ts' h2
  -- observeObject, anything else: refused
  case case2 =>
    intro ts target inCollection other hne h ts' heq
    simp only [observeObject] at heq
    cases heq
  -- observeMembers, no members left
  case case3 => intro ts target h ts' heq; simp only [observeMembers] at heq; cases heq; exact h
  -- a member that is an object, marked as a map
  case case4 =>
    intro ts target k tl here a hmap raw ihtl ihentries h ts' heq
    simp only [observeMembers] at heq
    rw [if_pos hmap] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    refine ihtl ts1 ?_ ts' hrest
    obtain ⟨_, _, hentries⟩ := except_bind_ok hin
    exact ihentries (Tables.upsert_ok (recordMember_ok h) (fun _ ht => ht)) ts1 hentries
  -- a member that is an object, not a map: a table of its own
  case case5 =>
    intro ts target k tl here a hmap ihtl ihobj h ts' heq
    simp only [observeMembers] at heq
    rw [if_neg hmap] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    refine ihtl ts1 ?_ ts' hrest
    exact ihobj (recordMember_ok h) ts1 hin
  -- a member that is an array
  case case6 =>
    intro ts target k tl here els ihtl ihelems h ts' heq
    simp only [observeMembers] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    refine ihtl ts1 ?_ ts' hrest
    exact ihelems (Tables.upsert_ok (recordMember_ok h) (fun _ ht => ht)) ts1 hin
  -- a member that is a scalar
  case case7 =>
    intro ts target k tl other hno1 hno2 ihtl h ts' heq
    simp only [observeMembers] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    refine ihtl ts1 ?_ ts' hrest
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    exact recordMember_ok h
  -- observeElems, no elements left
  case case8 => intro ts elemTable raw h ts' heq; simp only [observeElems] at heq; cases heq; exact h
  case case9 =>
    intro ts elemTable raw tl a _ ihtl ihobj h ts' heq
    simp only [observeElems] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    exact ihtl ts1 (ihobj h ts1 hin) ts' hrest
  case case10 =>
    intro ts elemTable raw tl els _ h ts' heq
    simp only [observeElems] at heq
    obtain ⟨_, hin, _⟩ := except_bind_ok heq
    cases hin
  case case11 =>
    intro ts elemTable raw tl other hno1 hno2 ihtl h ts' heq
    simp only [observeElems] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    refine ihtl ts1 ?_ ts' hrest
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    exact recordMember_ok (Tables.upsert_ok h (keep (fun _ => rfl)))
  -- observeEntries, no entries left
  case case12 => intro ts entryTable raw h ts' heq; simp only [observeEntries] at heq; cases heq; exact h
  case case13 =>
    intro ts entryTable raw k tl a _ ihtl ihobj h ts' heq
    simp only [observeEntries] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    exact ihtl ts1 (ihobj h ts1 hin) ts' hrest
  case case14 =>
    intro ts entryTable raw k tl els ihtl h ts' heq
    simp only [observeEntries] at heq
    obtain ⟨_, hin, _⟩ := except_bind_ok heq
    cases hin
  case case15 =>
    intro ts entryTable raw k tl other hno1 hno2 ihtl h ts' heq
    simp only [observeEntries] at heq
    obtain ⟨ts1, hin, hrest⟩ := except_bind_ok heq
    refine ihtl ts1 ?_ ts' hrest
    obtain ⟨_, _, hrec⟩ := except_bind_ok hin
    cases hrec
    exact recordMember_ok (Tables.upsert_ok h (keep (fun _ => rfl)))

/-- One document, observed from nothing, comes out in order. -/
theorem observeDocument_ok {cfg : Config} {d : Doc} {ts : Tables}
    (h : observeDocument cfg d = .ok ts) : TablesOk ts :=
  observe_ok cfg [] [] false d TablesOk.nil ts h

/-- `inferFinish` checks the corpus and then rewrites only the absence
    counts, so the order survives it. -/
theorem inferFinish_ok {cfg : Config} {ts ts' : Tables} (hok : TablesOk ts)
    (h : inferFinish cfg ts = .ok ts') : TablesOk ts' := by
  unfold inferFinish at h
  obtain ⟨_, _, h1⟩ := except_bind_ok h
  obtain ⟨_, _, h2⟩ := except_bind_ok h1
  obtain ⟨_, _, h3⟩ := except_bind_ok h2
  cases h3
  refine ⟨sortedBy_map (fun pr => by obtain ⟨p, t⟩ := pr; rfl) ts hok.1,
          allV_map ?_ ts hok.2⟩
  intro pr hpr
  obtain ⟨p, t⟩ := pr
  exact ⟨sortedBy_map (fun q => by obtain ⟨k, o⟩ := q; rfl) t.members hpr.1,
         allV_map (fun q hq => by obtain ⟨k, o⟩ := q; exact hq) t.members hpr.2⟩

/-- Everything inference builds is in order. -/
theorem inferCorpus_ok {cfg : Config} {ds : List Doc} {ts : Tables}
    (h : inferCorpus cfg ds = .ok ts) : TablesOk ts := by
  unfold inferCorpus at h
  obtain ⟨tss, hm, hf⟩ := except_bind_ok h
  refine inferFinish_ok ?_ hf
  -- the fold starts in order and every step preserves it
  have : ∀ l : List Tables, (∀ x, x ∈ l → TablesOk x) → ∀ b, TablesOk b →
      TablesOk (l.foldl Tables.merge b) := by
    intro l
    induction l with
    | nil => intro _ b hb; exact hb
    | cons x xs ih =>
        intro hall b hb
        exact ih (fun y hy => hall y (List.mem_cons_of_mem _ hy)) _
          (Tables.merge_ok hb (hall x (List.mem_cons_self ..)))
  exact this tss (fun t ht => by
    obtain ⟨d, _, hd⟩ := mem_of_mapM_ok hm t ht
    exact observeDocument_ok hd) [] TablesOk.nil

end Tatami
