import Tatami.Sorted

/-!
# Merging sorted association lists

`Tables.merge`, `TableObs.merge` and `Obs.merge` are all `mergeBy` or
`unionBy` at bottom, so `infer_perm` reduces to these being commutative and
associative -- given that the key order is strict and total, and that the
combining function is itself commutative and associative.

The order is a hypothesis rather than a class because the three uses want
three different comparisons: `Path.lt` on tables, `String`'s `<` on members,
and `Ty.lt` on the set of observed types.
-/

namespace Tatami

variable {K V : Type}

/-- The only fact about `Except` the proofs need: a successful bind means
    both halves succeeded. Here because several files want it. -/
theorem except_bind_ok {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {b : β}
    (h : (x >>= g) = .ok b) : ∃ a, x = .ok a ∧ g a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ## Generic facts about `mapM` over `Except`

    Here rather than in one of the files that uses them, because two do. -/

theorem mem_of_mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → ∀ b, b ∈ r → ∃ a, a ∈ l ∧ f a = .ok b := by
  intro l
  induction l with
  | nil =>
      intro r h b hb
      rw [List.mapM_nil] at h; cases h; cases hb
  | cons a as ih =>
      intro r h b hb
      rw [List.mapM_cons] at h
      obtain ⟨x, hfa, h1⟩ := except_bind_ok h
      obtain ⟨y, hm, h2⟩ := except_bind_ok h1
      cases h2
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact ⟨a, by simp, hfa⟩
      · obtain ⟨a', ha', hfa'⟩ := ih hm b hb'
        exact ⟨a', by simp [ha'], hfa'⟩

/-- Membership the other way: every input has an output. `mem_of_mapM_ok`
    finds the table a module came from; this finds the module a table went
    to. -/
theorem mapM_ok_pointwise {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r →
      ∀ a, a ∈ l → ∃ b, b ∈ r ∧ f a = .ok b := by
  intro l
  induction l with
  | nil => intro r _ a ha; cases ha
  | cons x xs ih =>
      intro r h a ha
      rw [List.mapM_cons] at h
      obtain ⟨b, hfx, h1⟩ := except_bind_ok h
      obtain ⟨bs, hm, h2⟩ := except_bind_ok h1
      cases h2
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨b, by simp, hfx⟩
      · obtain ⟨b', hb', hfb'⟩ := ih hm a ha'
        exact ⟨b', by simp [hb'], hfb'⟩

/-- `mapM` respects a pointwise equality: if `f` sends every input to an
    output agreeing under `g` and `k`, the whole list agrees. -/
theorem mapM_ok_map {α β γ ε : Type} {f : α → Except ε β} {g : β → γ} {k : α → γ}
    (hgk : ∀ a b, f a = .ok b → g b = k a) :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.map g = l.map k := by
  intro l
  induction l with
  | nil => intro r h; rw [List.mapM_nil] at h; cases h; rfl
  | cons a as ih =>
      intro r h
      rw [List.mapM_cons] at h
      obtain ⟨b, hfa, h1⟩ := except_bind_ok h
      obtain ⟨bs, hm, h2⟩ := except_bind_ok h1
      cases h2
      rw [List.map_cons, List.map_cons, ih hm, hgk a b hfa]



/-- What `mergeBy` needs of its key order: `eqk` decides equality, and `lt` is
    a strict total order, so of any two distinct keys exactly one is smaller. -/
structure StrictOrder (lt : K → K → Bool) (eqk : K → K → Bool) : Prop where
  eq_iff : ∀ a b, eqk a b = true ↔ a = b
  asymm  : ∀ a b, lt a b = true → lt b a = false
  total  : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true
  trans  : ∀ a b c, lt a b = true → lt b c = true → lt a c = true

/-- Irreflexivity is not an extra assumption: if `lt a a` held, asymmetry
    would make it fail. -/
theorem StrictOrder.irrefl {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) (a : K) :
    lt a a = false := by
  cases h : lt a a with
  | false => rfl
  | true => have hn := ho.asymm a a h; rw [h] at hn; exact hn

theorem StrictOrder.eq_symm {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk)
    (a b : K) : eqk a b = eqk b a := by
  cases hab : eqk a b <;> cases hba : eqk b a <;> try rfl
  · have hba' : b = a := (ho.eq_iff b a).mp hba
    subst hba'
    rw [(ho.eq_iff b b).mpr rfl] at hab
    cases hab
  · have hab' : a = b := (ho.eq_iff a b).mp hab
    subst hab'
    rw [(ho.eq_iff a a).mpr rfl] at hba
    cases hba

/-- Merging is commutative: the order decides which key comes first, and it
    gives the same answer whichever list it is asked about. -/
theorem mergeBy_comm {lt eqk : K → K → Bool} {combine : V → V → V}
    (ho : StrictOrder lt eqk) (hc : ∀ x y, combine x y = combine y x) :
    ∀ a b, mergeBy lt eqk combine a b = mergeBy lt eqk combine b a := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [mergeBy]
  | cons pa as iha =>
      intro b
      induction b with
      | nil => simp [mergeBy]
      | cons pb bs ihb =>
          obtain ⟨ka, va⟩ := pa
          obtain ⟨kb, vb⟩ := pb
          rw [mergeBy, mergeBy]
          rw [ho.eq_symm kb ka]
          by_cases heq : eqk ka kb = true
          · rw [if_pos heq, if_pos heq]
            have hk : ka = kb := (ho.eq_iff ka kb).mp heq
            subst hk
            rw [hc va vb, iha bs]
          · rw [if_neg heq, if_neg heq]
            have hne : ka ≠ kb := fun h => heq ((ho.eq_iff ka kb).mpr h)
            by_cases hlt : lt ka kb = true
            · rw [if_pos hlt, if_neg (by rw [ho.asymm ka kb hlt]; simp)]
              rw [iha ((kb, vb) :: bs)]
            · rw [if_neg hlt]
              have hgt : lt kb ka = true := by
                rcases ho.total ka kb hne with h | h
                · exact absurd h hlt
                · exact h
              rw [if_pos hgt, ihb]

/-- The same for a set, which is the same merge with nothing to combine. -/
theorem unionBy_comm {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) :
    ∀ a b, unionBy lt eqk a b = unionBy lt eqk b a := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [unionBy]
  | cons x as iha =>
      intro b
      induction b with
      | nil => simp [unionBy]
      | cons y bs ihb =>
          rw [unionBy, unionBy]
          rw [ho.eq_symm y x]
          by_cases heq : eqk x y = true
          · rw [if_pos heq, if_pos heq]
            have hk : x = y := (ho.eq_iff x y).mp heq
            subst hk
            rw [iha bs]
          · rw [if_neg heq, if_neg heq]
            have hne : x ≠ y := fun h => heq ((ho.eq_iff x y).mpr h)
            by_cases hlt : lt x y = true
            · rw [if_pos hlt, if_neg (by rw [ho.asymm x y hlt]; simp)]
              rw [iha (y :: bs)]
            · rw [if_neg hlt]
              have hgt : lt y x = true := by
                rcases ho.total x y hne with h | h
                · exact absurd h hlt
                · exact h
              rw [if_pos hgt, ihb]

/-! ## Merging, read through lookups

    Commutativity above was a direct induction. Associativity that way is nine
    top-level cases over three lists, so it is done differently: a merge is
    characterised by what it looks up, two sorted lists that look up the same
    are equal, and both laws then follow from the same laws for `Option`,
    which are immediate.

    The characterisation needs the arguments sorted -- without it a key could
    appear twice and a lookup would see only the first. -/

/-- What one key maps to. `List.lookup` wants a `BEq` instance; the order is
    passed in here like everything else. -/
def lookupBy (eqk : K → K → Bool) (k : K) : List (K × V) → Option V
  | [] => none
  | (k', v) :: tl => if eqk k k' then some v else lookupBy eqk k tl

/-- Every key in the list is above `k`. -/
def Below (lt : K → K → Bool) (k : K) : List (K × V) → Prop
  | [] => True
  | p :: tl => lt k p.1 = true ∧ Below lt k tl

/-- Keys strictly increasing, in the "head below the rest" form rather than
    the chain form: it is what the lookup argument actually uses. -/
def SortedBy (lt : K → K → Bool) : List (K × V) → Prop
  | [] => True
  | p :: tl => Below lt p.1 tl ∧ SortedBy lt tl

/-- Every value satisfies `P`. -/
def AllV (P : V → Prop) : List (K × V) → Prop
  | [] => True
  | p :: tl => P p.2 ∧ AllV P tl

/-- Transitivity carries `Below` down from a smaller key. -/
theorem below_of_lt {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) {j k : K} :
    ∀ {l : List (K × V)}, Below lt k l → lt j k = true → Below lt j l := by
  intro l
  induction l with
  | nil => intro _ _; trivial
  | cons p tl ih =>
      intro hb hjk
      exact ⟨ho.trans j k p.1 hjk hb.1, ih hb.2 hjk⟩

/-- A key below everything in the list is not in it. -/
theorem lookupBy_of_below {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) {k : K} :
    ∀ {l : List (K × V)}, Below lt k l → lookupBy eqk k l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p tl ih =>
      intro hb
      obtain ⟨k', v⟩ := p
      have hb1 : lt k k' = true := hb.1
      rw [lookupBy, if_neg, ih hb.2]
      intro hEq
      have hkk : k = k' := (ho.eq_iff k k').mp hEq
      subst hkk
      rw [ho.irrefl k] at hb1
      exact Bool.noConfusion hb1

/-- The head of a sorted list is below its tail, so its key looks up to its
    own value and nothing else. -/
theorem lookupBy_head {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk)
    {k : K} {v : V} {tl : List (K × V)} (hs : SortedBy lt ((k, v) :: tl)) :
    lookupBy eqk k ((k, v) :: tl) = some v := by
  rw [lookupBy, if_pos ((ho.eq_iff k k).mpr rfl)]

/-- Two sorted lists that agree on every lookup are the same list. -/
theorem sorted_ext {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) :
    ∀ {a b : List (K × V)}, SortedBy lt a → SortedBy lt b →
      (∀ k, lookupBy eqk k a = lookupBy eqk k b) → a = b := by
  intro a
  induction a with
  | nil =>
      intro b _ _ hlk
      cases b with
      | nil => rfl
      | cons q bs =>
          obtain ⟨kb, vb⟩ := q
          have := hlk kb
          rw [lookupBy, lookupBy, if_pos ((ho.eq_iff kb kb).mpr rfl)] at this
          exact absurd this (by simp)
  | cons p as ih =>
      intro b hsa hsb hlk
      obtain ⟨ka, va⟩ := p
      cases b with
      | nil =>
          have := hlk ka
          rw [lookupBy, lookupBy, if_pos ((ho.eq_iff ka ka).mpr rfl)] at this
          exact absurd this (by simp)
      | cons q bs =>
          obtain ⟨kb, vb⟩ := q
          -- the two heads must be the same key: each is below its own tail,
          -- so a strictly smaller head would look up to `none` in the other
          have hkab : ka = kb := by
            by_cases hEq : ka = kb
            · exact hEq
            exfalso
            rcases ho.total ka kb hEq with hlt | hlt
            · have hb : Below lt ka ((kb, vb) :: bs) :=
                ⟨hlt, below_of_lt ho hsb.1 hlt⟩
              have h1 := hlk ka
              rw [lookupBy, if_pos ((ho.eq_iff ka ka).mpr rfl),
                  lookupBy_of_below ho hb] at h1
              exact absurd h1 (by simp)
            · have hb : Below lt kb ((ka, va) :: as) :=
                ⟨hlt, below_of_lt ho hsa.1 hlt⟩
              have h1 := hlk kb
              rw [lookupBy_of_below ho hb, lookupBy,
                  if_pos ((ho.eq_iff kb kb).mpr rfl)] at h1
              exact absurd h1 (by simp)
          subst hkab
          have hv : va = vb := by
            have h1 := hlk ka
            rw [lookupBy, lookupBy, if_pos ((ho.eq_iff ka ka).mpr rfl),
                if_pos ((ho.eq_iff ka ka).mpr rfl)] at h1
            exact Option.some.inj h1
          subst hv
          have hrest : ∀ k, lookupBy eqk k as = lookupBy eqk k bs := by
            intro k
            by_cases hk : eqk k ka = true
            · have hka : k = ka := (ho.eq_iff k ka).mp hk
              subst hka
              rw [lookupBy_of_below ho hsa.1, lookupBy_of_below ho hsb.1]
            · have h1 := hlk k
              rw [lookupBy, lookupBy, if_neg hk, if_neg hk] at h1
              exact h1
          rw [ih hsa.2 hsb.2 hrest]

/-- Combining two lookups: present on one side wins, present on both combines. -/
def combineOpt (combine : V → V → V) : Option V → Option V → Option V
  | none, y => y
  | some x, none => some x
  | some x, some y => some (combine x y)

theorem combineOpt_comm {combine : V → V → V} (hc : ∀ x y, combine x y = combine y x) :
    ∀ x y, combineOpt combine x y = combineOpt combine y x := by
  intro x y; cases x <;> cases y <;> simp [combineOpt, hc]

theorem combineOpt_assoc {combine : V → V → V}
    (ha : ∀ x y z, combine (combine x y) z = combine x (combine y z)) :
    ∀ x y z, combineOpt combine (combineOpt combine x y) z
           = combineOpt combine x (combineOpt combine y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> simp [combineOpt, ha]

/-- A key below both lists is below their merge. -/
theorem mergeBy_below {lt eqk : K → K → Bool} {combine : V → V → V} {j : K} :
    ∀ a b : List (K × V), Below lt j a → Below lt j b →
      Below lt j (mergeBy lt eqk combine a b) := by
  intro a
  induction a with
  | nil => intro b _ hb; rw [mergeBy]; exact hb
  | cons pa as iha =>
      intro b
      induction b with
      | nil =>
          intro ha _
          rw [mergeBy]
          · exact ha
          · simp
      | cons pb bs ihb =>
          intro ha hb
          obtain ⟨ka, va⟩ := pa
          obtain ⟨kb, vb⟩ := pb
          rw [mergeBy]
          by_cases heq : eqk ka kb = true
          · rw [if_pos heq]
            exact ⟨ha.1, iha bs ha.2 hb.2⟩
          · rw [if_neg heq]
            by_cases hlt : lt ka kb = true
            · rw [if_pos hlt]; exact ⟨ha.1, iha ((kb, vb) :: bs) ha.2 hb⟩
            · rw [if_neg hlt]; exact ⟨hb.1, ihb ha hb.2⟩

/-- Merging two sorted lists gives a sorted list. -/
theorem mergeBy_sorted {lt eqk : K → K → Bool} {combine : V → V → V}
    (ho : StrictOrder lt eqk) :
    ∀ a b : List (K × V), SortedBy lt a → SortedBy lt b →
      SortedBy lt (mergeBy lt eqk combine a b) := by
  intro a
  induction a with
  | nil => intro b _ hb; rw [mergeBy]; exact hb
  | cons pa as iha =>
      intro b
      induction b with
      | nil =>
          intro ha _
          rw [mergeBy]
          · exact ha
          · simp
      | cons pb bs ihb =>
          intro hsa hsb
          obtain ⟨ka, va⟩ := pa
          obtain ⟨kb, vb⟩ := pb
          have hgt : eqk ka kb ≠ true → lt ka kb ≠ true → lt kb ka = true := by
            intro heq hlt
            rcases ho.total ka kb (fun h => heq ((ho.eq_iff ka kb).mpr h)) with h | h
            · exact absurd h hlt
            · exact h
          rw [mergeBy]
          by_cases heq : eqk ka kb = true
          · have hk : ka = kb := (ho.eq_iff ka kb).mp heq
            subst hk
            rw [if_pos heq]
            exact ⟨mergeBy_below as bs hsa.1 hsb.1, iha bs hsa.2 hsb.2⟩
          · rw [if_neg heq]
            by_cases hlt : lt ka kb = true
            · rw [if_pos hlt]
              have hb : Below lt ka ((kb, vb) :: bs) := ⟨hlt, below_of_lt ho hsb.1 hlt⟩
              exact ⟨mergeBy_below as _ hsa.1 hb, iha _ hsa.2 hsb⟩
            · rw [if_neg hlt]
              have ha : Below lt kb ((ka, va) :: as) :=
                ⟨hgt heq hlt, below_of_lt ho hsa.1 (hgt heq hlt)⟩
              exact ⟨mergeBy_below _ bs ha hsb.1, ihb hsa hsb.2⟩

/-- What a merge looks up: the two lookups, combined. This is the whole
    content of `mergeBy`, and both laws below read it off. -/
theorem mergeBy_lookup {lt eqk : K → K → Bool} {combine : V → V → V}
    (ho : StrictOrder lt eqk) :
    ∀ a b : List (K × V), SortedBy lt a → SortedBy lt b → ∀ k,
      lookupBy eqk k (mergeBy lt eqk combine a b)
        = combineOpt combine (lookupBy eqk k a) (lookupBy eqk k b) := by
  intro a
  induction a with
  | nil => intro b _ _ k; rw [mergeBy]; simp [lookupBy, combineOpt]
  | cons pa as iha =>
      intro b
      induction b with
      | nil =>
          intro _ _ k
          rw [mergeBy]
          · cases h : lookupBy eqk k (pa :: as) <;> simp [lookupBy, combineOpt, h]
          · simp
      | cons pb bs ihb =>
          intro hsa hsb k
          obtain ⟨ka, va⟩ := pa
          obtain ⟨kb, vb⟩ := pb
          have hgt : eqk ka kb ≠ true → lt ka kb ≠ true → lt kb ka = true := by
            intro heq hlt
            rcases ho.total ka kb (fun h => heq ((ho.eq_iff ka kb).mpr h)) with h | h
            · exact absurd h hlt
            · exact h
          rw [mergeBy]
          by_cases heq : eqk ka kb = true
          · have hk : ka = kb := (ho.eq_iff ka kb).mp heq
            subst hk
            rw [if_pos heq, lookupBy, lookupBy, lookupBy]
            by_cases hk2 : eqk k ka = true
            · rw [if_pos hk2, if_pos hk2, if_pos hk2]; rfl
            · rw [if_neg hk2, if_neg hk2, if_neg hk2]
              exact iha bs hsa.2 hsb.2 k
          · rw [if_neg heq]
            by_cases hlt : lt ka kb = true
            · rw [if_pos hlt]
              by_cases hk2 : eqk k ka = true
              · have hka : k = ka := (ho.eq_iff k ka).mp hk2
                subst hka
                have hb : Below lt k ((kb, vb) :: bs) := ⟨hlt, below_of_lt ho hsb.1 hlt⟩
                rw [lookupBy, if_pos hk2, lookupBy, if_pos hk2,
                    lookupBy_of_below ho hb]
                rfl
              · have e1 : lookupBy eqk k
                      ((ka, va) :: mergeBy lt eqk combine as ((kb, vb) :: bs))
                    = lookupBy eqk k (mergeBy lt eqk combine as ((kb, vb) :: bs)) := by
                  rw [lookupBy, if_neg hk2]
                have e2 : lookupBy eqk k ((ka, va) :: as) = lookupBy eqk k as := by
                  rw [lookupBy, if_neg hk2]
                rw [e1, e2]
                exact iha ((kb, vb) :: bs) hsa.2 hsb k
            · rw [if_neg hlt]
              by_cases hk2 : eqk k kb = true
              · have hkb : k = kb := (ho.eq_iff k kb).mp hk2
                subst hkb
                have ha : Below lt k ((ka, va) :: as) :=
                  ⟨hgt heq hlt, below_of_lt ho hsa.1 (hgt heq hlt)⟩
                rw [lookupBy, if_pos hk2, lookupBy_of_below ho ha, lookupBy,
                    if_pos hk2]
                rfl
              · have e1 : lookupBy eqk k
                      ((kb, vb) :: mergeBy lt eqk combine ((ka, va) :: as) bs)
                    = lookupBy eqk k (mergeBy lt eqk combine ((ka, va) :: as) bs) := by
                  rw [lookupBy, if_neg hk2]
                have e2 : lookupBy eqk k ((kb, vb) :: bs) = lookupBy eqk k bs := by
                  rw [lookupBy, if_neg hk2]
                rw [e1, e2]
                exact ihb hsa hsb.2 k

/-- Merging is associative on sorted lists, because combining lookups is. -/
theorem mergeBy_assoc {lt eqk : K → K → Bool} {combine : V → V → V}
    (ho : StrictOrder lt eqk)
    (hca : ∀ x y z, combine (combine x y) z = combine x (combine y z)) :
    ∀ a b c : List (K × V), SortedBy lt a → SortedBy lt b → SortedBy lt c →
      mergeBy lt eqk combine (mergeBy lt eqk combine a b) c
        = mergeBy lt eqk combine a (mergeBy lt eqk combine b c) := by
  intro a b c hsa hsb hsc
  have hab : SortedBy lt (mergeBy lt eqk combine a b) := mergeBy_sorted ho a b hsa hsb
  have hbc : SortedBy lt (mergeBy lt eqk combine b c) := mergeBy_sorted ho b c hsb hsc
  refine sorted_ext ho (mergeBy_sorted ho _ c hab hsc)
    (mergeBy_sorted ho a _ hsa hbc) ?_
  intro k
  rw [mergeBy_lookup ho _ c hab hsc k, mergeBy_lookup ho a b hsa hsb k,
      mergeBy_lookup ho a _ hsa hbc k, mergeBy_lookup ho b c hsb hsc k]
  exact combineOpt_assoc hca _ _ _

/-- The form the corpus fold actually needs: two merges into an accumulator
    commute. It is `mergeBy_assoc` and `mergeBy_comm` together, and it is what
    `foldl_perm` in `Proofs.Inference` takes as its hypothesis. -/
theorem mergeBy_right_comm {lt eqk : K → K → Bool} {combine : V → V → V}
    (ho : StrictOrder lt eqk)
    (hc : ∀ x y, combine x y = combine y x)
    (hca : ∀ x y z, combine (combine x y) z = combine x (combine y z)) :
    ∀ b x y : List (K × V), SortedBy lt b → SortedBy lt x → SortedBy lt y →
      mergeBy lt eqk combine (mergeBy lt eqk combine b x) y
        = mergeBy lt eqk combine (mergeBy lt eqk combine b y) x := by
  intro b x y hsb hsx hsy
  rw [mergeBy_assoc ho hca b x y hsb hsx hsy,
      mergeBy_assoc ho hca b y x hsb hsy hsx,
      mergeBy_comm ho hc x y]

/-! ## Inserting one entry

    The walk builds its observations with `insertBy`, one member at a time, so
    the order invariant has to survive that as well as the merge. -/

theorem insertBy_below {lt eqk : K → K → Bool} {combine : V → V → V} {j k : K} {v : V} :
    ∀ l : List (K × V), Below lt j l → lt j k = true →
      Below lt j (insertBy lt eqk combine k v l) := by
  intro l
  induction l with
  | nil => intro _ hjk; exact ⟨hjk, trivial⟩
  | cons p tl ih =>
      intro hb hjk
      obtain ⟨k', v'⟩ := p
      rw [insertBy]
      by_cases heq : eqk k k' = true
      · rw [if_pos heq]; exact hb
      · rw [if_neg heq]
        by_cases hlt : lt k k' = true
        · rw [if_pos hlt]; exact ⟨hjk, hb⟩
        · rw [if_neg hlt]; exact ⟨hb.1, ih hb.2 hjk⟩

theorem insertBy_sorted {lt eqk : K → K → Bool} {combine : V → V → V}
    (ho : StrictOrder lt eqk) {k : K} {v : V} :
    ∀ l : List (K × V), SortedBy lt l → SortedBy lt (insertBy lt eqk combine k v l) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨trivial, trivial⟩
  | cons p tl ih =>
      intro hs
      obtain ⟨k', v'⟩ := p
      rw [insertBy]
      by_cases heq : eqk k k' = true
      · rw [if_pos heq]; exact hs
      · rw [if_neg heq]
        by_cases hlt : lt k k' = true
        · rw [if_pos hlt]
          exact ⟨⟨hlt, below_of_lt ho hs.1 hlt⟩, hs⟩
        · rw [if_neg hlt]
          have hgt : lt k' k = true := by
            rcases ho.total k k' (fun h => heq ((ho.eq_iff k k').mpr h)) with h | h
            · exact absurd h hlt
            · exact h
          exact ⟨insertBy_below tl hs.1 hgt, ih hs.2⟩

theorem insertBy_allV {lt eqk : K → K → Bool} {combine : V → V → V} {P : V → Prop}
    (hP : ∀ x y, P x → P y → P (combine x y)) {k : K} {v : V} (hv : P v) :
    ∀ l : List (K × V), AllV P l → AllV P (insertBy lt eqk combine k v l) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨hv, trivial⟩
  | cons p tl ih =>
      intro ha
      obtain ⟨k', v'⟩ := p
      rw [insertBy]
      by_cases heq : eqk k k' = true
      · rw [if_pos heq]; exact ⟨hP v' v ha.1 hv, ha.2⟩
      · rw [if_neg heq]
        by_cases hlt : lt k k' = true
        · rw [if_pos hlt]; exact ⟨hv, ha⟩
        · rw [if_neg hlt]; exact ⟨ha.1, ih ha.2⟩

/-! ## Rewriting values in place

    `Tables.upsert` updates an existing entry by mapping over the list, which
    leaves every key where it was. -/

theorem below_map {lt : K → K → Bool} {j : K} {g : K × V → K × V}
    (hg : ∀ p, (g p).1 = p.1) : ∀ l : List (K × V), Below lt j l → Below lt j (l.map g) := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons p tl ih => intro hb; exact ⟨by rw [hg p]; exact hb.1, ih hb.2⟩

theorem sortedBy_map {lt : K → K → Bool} {g : K × V → K × V}
    (hg : ∀ p, (g p).1 = p.1) :
    ∀ l : List (K × V), SortedBy lt l → SortedBy lt (l.map g) := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons p tl ih =>
      intro hs
      exact ⟨by rw [hg p]; exact below_map hg tl hs.1, ih hs.2⟩

theorem allV_map {P : V → Prop} {g : K × V → K × V} (hg : ∀ p, P p.2 → P (g p).2) :
    ∀ l : List (K × V), AllV P l → AllV P (l.map g) := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons p tl ih => intro ha; exact ⟨hg p ha.1, ih ha.2⟩

/-! ## Merging under a value invariant

    `Obs.merge` is associative only where the type sets it unions are sorted,
    so the laws above are too strong to instantiate directly: their `combine`
    hypotheses are unconditional. These carry a predicate on values through
    the merge instead. -/

theorem mergeBy_allV {lt eqk : K → K → Bool} {combine : V → V → V} {P : V → Prop}
    (hP : ∀ x y, P x → P y → P (combine x y)) :
    ∀ a b : List (K × V), AllV P a → AllV P b → AllV P (mergeBy lt eqk combine a b) := by
  intro a
  induction a with
  | nil => intro b _ hb; rw [mergeBy]; exact hb
  | cons pa as iha =>
      intro b
      induction b with
      | nil =>
          intro ha _
          rw [mergeBy]
          · exact ha
          · simp
      | cons pb bs ihb =>
          intro ha hb
          obtain ⟨ka, va⟩ := pa
          obtain ⟨kb, vb⟩ := pb
          rw [mergeBy]
          by_cases heq : eqk ka kb = true
          · rw [if_pos heq]; exact ⟨hP va vb ha.1 hb.1, iha bs ha.2 hb.2⟩
          · rw [if_neg heq]
            by_cases hlt : lt ka kb = true
            · rw [if_pos hlt]; exact ⟨ha.1, iha ((kb, vb) :: bs) ha.2 hb⟩
            · rw [if_neg hlt]; exact ⟨hb.1, ihb ha hb.2⟩

theorem lookupBy_allV {eqk : K → K → Bool} {P : V → Prop} {k : K} {v : V} :
    ∀ {l : List (K × V)}, AllV P l → lookupBy eqk k l = some v → P v := by
  intro l
  induction l with
  | nil => intro _ h; rw [lookupBy] at h; cases h
  | cons p tl ih =>
      intro hall h
      obtain ⟨k', v'⟩ := p
      rw [lookupBy] at h
      by_cases hk : eqk k k' = true
      · rw [if_pos hk] at h; cases h; exact hall.1
      · rw [if_neg hk] at h; exact ih hall.2 h

/-- Associativity where the combining laws hold only of values satisfying `P`,
    which is what `Obs.merge` needs: it is associative on observations whose
    type sets are sorted, and not otherwise. -/
theorem mergeBy_assocOn {lt eqk : K → K → Bool} {combine : V → V → V} {P : V → Prop}
    (ho : StrictOrder lt eqk)
    (hP : ∀ x y, P x → P y → P (combine x y))
    (hca : ∀ x y z, P x → P y → P z → combine (combine x y) z = combine x (combine y z)) :
    ∀ a b c : List (K × V), SortedBy lt a → SortedBy lt b → SortedBy lt c →
      AllV P a → AllV P b → AllV P c →
      mergeBy lt eqk combine (mergeBy lt eqk combine a b) c
        = mergeBy lt eqk combine a (mergeBy lt eqk combine b c) := by
  intro a b c hsa hsb hsc hpa hpb hpc
  have hab : SortedBy lt (mergeBy lt eqk combine a b) := mergeBy_sorted ho a b hsa hsb
  have hbc : SortedBy lt (mergeBy lt eqk combine b c) := mergeBy_sorted ho b c hsb hsc
  refine sorted_ext ho (mergeBy_sorted ho _ c hab hsc)
    (mergeBy_sorted ho a _ hsa hbc) ?_
  intro k
  rw [mergeBy_lookup ho _ c hab hsc k, mergeBy_lookup ho a b hsa hsb k,
      mergeBy_lookup ho a _ hsa hbc k, mergeBy_lookup ho b c hsb hsc k]
  -- three lookups, each a `P` value where it is present
  cases hla : lookupBy eqk k a <;> cases hlb : lookupBy eqk k b <;>
    cases hlc : lookupBy eqk k c <;> simp only [combineOpt]
  exact congrArg some (hca _ _ _ (lookupBy_allV hpa hla) (lookupBy_allV hpb hlb)
    (lookupBy_allV hpc hlc))

/-- And commutativity, likewise. -/
theorem mergeBy_commOn {lt eqk : K → K → Bool} {combine : V → V → V} {P : V → Prop}
    (ho : StrictOrder lt eqk)
    (hc : ∀ x y, P x → P y → combine x y = combine y x) :
    ∀ a b : List (K × V), SortedBy lt a → SortedBy lt b → AllV P a → AllV P b →
      mergeBy lt eqk combine a b = mergeBy lt eqk combine b a := by
  intro a b hsa hsb hpa hpb
  refine sorted_ext ho (mergeBy_sorted ho a b hsa hsb) (mergeBy_sorted ho b a hsb hsa) ?_
  intro k
  rw [mergeBy_lookup ho a b hsa hsb k, mergeBy_lookup ho b a hsb hsa k]
  cases hla : lookupBy eqk k a <;> cases hlb : lookupBy eqk k b <;>
    simp only [combineOpt]
  exact congrArg some (hc _ _ (lookupBy_allV hpa hla) (lookupBy_allV hpb hlb))

/-! ## The same for a set

    `Obs.merge` unions the types seen at a member, which is `unionBy`. The
    development mirrors the one above with membership in place of lookup and
    `||` in place of `combineOpt`. -/

def BelowK (lt : K → K → Bool) (k : K) : List K → Prop
  | [] => True
  | x :: tl => lt k x = true ∧ BelowK lt k tl

def SortedK (lt : K → K → Bool) : List K → Prop
  | [] => True
  | x :: tl => BelowK lt x tl ∧ SortedK lt tl

def memBy (eqk : K → K → Bool) (k : K) : List K → Bool
  | [] => false
  | x :: tl => eqk k x || memBy eqk k tl

theorem belowK_of_lt {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) {j k : K} :
    ∀ {l : List K}, BelowK lt k l → lt j k = true → BelowK lt j l := by
  intro l
  induction l with
  | nil => intro _ _; trivial
  | cons x tl ih => intro hb hjk; exact ⟨ho.trans j k x hjk hb.1, ih hb.2 hjk⟩

theorem memBy_of_below {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) {k : K} :
    ∀ {l : List K}, BelowK lt k l → memBy eqk k l = false := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x tl ih =>
      intro hb
      have hb1 : lt k x = true := hb.1
      rw [memBy, ih hb.2, Bool.or_false]
      cases hEq : eqk k x with
      | false => rfl
      | true =>
          have hkx : k = x := (ho.eq_iff k x).mp hEq
          subst hkx
          rw [ho.irrefl k] at hb1
          exact absurd hb1 (by simp)

theorem sortedK_ext {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) :
    ∀ {a b : List K}, SortedK lt a → SortedK lt b →
      (∀ k, memBy eqk k a = memBy eqk k b) → a = b := by
  intro a
  induction a with
  | nil =>
      intro b _ _ hm
      cases b with
      | nil => rfl
      | cons y bs =>
          have := hm y
          rw [memBy, memBy, (ho.eq_iff y y).mpr rfl] at this
          exact absurd this (by simp)
  | cons x as ih =>
      intro b hsa hsb hm
      cases b with
      | nil =>
          have := hm x
          rw [memBy, memBy, (ho.eq_iff x x).mpr rfl] at this
          exact absurd this (by simp)
      | cons y bs =>
          have hxy : x = y := by
            by_cases hEq : x = y
            · exact hEq
            exfalso
            rcases ho.total x y hEq with hlt | hlt
            · have hb : BelowK lt x (y :: bs) := ⟨hlt, belowK_of_lt ho hsb.1 hlt⟩
              have h1 := hm x
              rw [memBy, (ho.eq_iff x x).mpr rfl, memBy_of_below ho hb] at h1
              exact absurd h1 (by simp)
            · have hb : BelowK lt y (x :: as) := ⟨hlt, belowK_of_lt ho hsa.1 hlt⟩
              have h1 := hm y
              rw [memBy_of_below ho hb, memBy, (ho.eq_iff y y).mpr rfl] at h1
              exact absurd h1 (by simp)
          subst hxy
          refine congrArg _ (ih hsa.2 hsb.2 ?_)
          intro k
          by_cases hk : eqk k x = true
          · have hkx : k = x := (ho.eq_iff k x).mp hk
            subst hkx
            rw [memBy_of_below ho hsa.1, memBy_of_below ho hsb.1]
          · have h1 := hm k
            rw [memBy, memBy] at h1
            simp only [Bool.not_eq_true] at hk
            rw [hk, Bool.false_or, Bool.false_or] at h1
            exact h1

theorem unionBy_belowK {lt eqk : K → K → Bool} {j : K} :
    ∀ a b : List K, BelowK lt j a → BelowK lt j b → BelowK lt j (unionBy lt eqk a b) := by
  intro a
  induction a with
  | nil => intro b _ hb; rw [unionBy]; exact hb
  | cons x as iha =>
      intro b
      induction b with
      | nil =>
          intro ha _
          rw [unionBy]
          · exact ha
          · simp
      | cons y bs ihb =>
          intro ha hb
          rw [unionBy]
          by_cases heq : eqk x y = true
          · rw [if_pos heq]; exact ⟨ha.1, iha bs ha.2 hb.2⟩
          · rw [if_neg heq]
            by_cases hlt : lt x y = true
            · rw [if_pos hlt]; exact ⟨ha.1, iha (y :: bs) ha.2 hb⟩
            · rw [if_neg hlt]; exact ⟨hb.1, ihb ha hb.2⟩

theorem unionBy_sorted {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) :
    ∀ a b : List K, SortedK lt a → SortedK lt b → SortedK lt (unionBy lt eqk a b) := by
  intro a
  induction a with
  | nil => intro b _ hb; rw [unionBy]; exact hb
  | cons x as iha =>
      intro b
      induction b with
      | nil =>
          intro ha _
          rw [unionBy]
          · exact ha
          · simp
      | cons y bs ihb =>
          intro hsa hsb
          have hgt : eqk x y ≠ true → lt x y ≠ true → lt y x = true := by
            intro heq hlt
            rcases ho.total x y (fun h => heq ((ho.eq_iff x y).mpr h)) with h | h
            · exact absurd h hlt
            · exact h
          rw [unionBy]
          by_cases heq : eqk x y = true
          · have hk : x = y := (ho.eq_iff x y).mp heq
            subst hk
            rw [if_pos heq]
            exact ⟨unionBy_belowK as bs hsa.1 hsb.1, iha bs hsa.2 hsb.2⟩
          · rw [if_neg heq]
            by_cases hlt : lt x y = true
            · rw [if_pos hlt]
              have hb : BelowK lt x (y :: bs) := ⟨hlt, belowK_of_lt ho hsb.1 hlt⟩
              exact ⟨unionBy_belowK as _ hsa.1 hb, iha _ hsa.2 hsb⟩
            · rw [if_neg hlt]
              have ha : BelowK lt y (x :: as) :=
                ⟨hgt heq hlt, belowK_of_lt ho hsa.1 (hgt heq hlt)⟩
              exact ⟨unionBy_belowK _ bs ha hsb.1, ihb hsa hsb.2⟩

theorem unionBy_mem {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) :
    ∀ a b : List K, SortedK lt a → SortedK lt b → ∀ k,
      memBy eqk k (unionBy lt eqk a b) = (memBy eqk k a || memBy eqk k b) := by
  intro a
  induction a with
  | nil => intro b _ _ k; rw [unionBy, memBy, Bool.false_or]
  | cons x as iha =>
      intro b
      induction b with
      | nil =>
          intro _ _ k
          rw [unionBy]
          · simp [memBy]
          · simp
      | cons y bs ihb =>
          intro hsa hsb k
          have hgt : eqk x y ≠ true → lt x y ≠ true → lt y x = true := by
            intro heq hlt
            rcases ho.total x y (fun h => heq ((ho.eq_iff x y).mpr h)) with h | h
            · exact absurd h hlt
            · exact h
          rw [unionBy]
          by_cases heq : eqk x y = true
          · have hk : x = y := (ho.eq_iff x y).mp heq
            subst hk
            rw [if_pos heq, memBy, memBy, memBy, iha bs hsa.2 hsb.2 k]
            cases eqk k x <;> simp
          · rw [if_neg heq]
            by_cases hlt : lt x y = true
            · rw [if_pos hlt, memBy, memBy, iha (y :: bs) hsa.2 hsb k]
              by_cases hk2 : eqk k x = true
              · have hkx : k = x := (ho.eq_iff k x).mp hk2
                subst hkx
                have hb : BelowK lt k (y :: bs) := ⟨hlt, belowK_of_lt ho hsb.1 hlt⟩
                rw [hk2, memBy_of_below ho hb]
                simp
              · simp only [Bool.not_eq_true] at hk2
                rw [hk2]; simp
            · rw [if_neg hlt, memBy, ihb hsa hsb.2 k]
              by_cases hk2 : eqk k y = true
              · have hky : k = y := (ho.eq_iff k y).mp hk2
                subst hky
                have ha : BelowK lt k (x :: as) :=
                  ⟨hgt heq hlt, belowK_of_lt ho hsa.1 (hgt heq hlt)⟩
                rw [hk2, memBy_of_below ho ha, memBy, hk2]
                simp
              · simp only [Bool.not_eq_true] at hk2
                simp [memBy, hk2]

theorem unionBy_assoc {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) :
    ∀ a b c : List K, SortedK lt a → SortedK lt b → SortedK lt c →
      unionBy lt eqk (unionBy lt eqk a b) c = unionBy lt eqk a (unionBy lt eqk b c) := by
  intro a b c hsa hsb hsc
  have hab : SortedK lt (unionBy lt eqk a b) := unionBy_sorted ho a b hsa hsb
  have hbc : SortedK lt (unionBy lt eqk b c) := unionBy_sorted ho b c hsb hsc
  refine sortedK_ext ho (unionBy_sorted ho _ c hab hsc)
    (unionBy_sorted ho a _ hsa hbc) ?_
  intro k
  rw [unionBy_mem ho _ c hab hsc k, unionBy_mem ho a b hsa hsb k,
      unionBy_mem ho a _ hsa hbc k, unionBy_mem ho b c hsb hsc k, Bool.or_assoc]

theorem allV_mem {P : V → Prop} : ∀ {l : List (K × V)} {p : K × V},
    AllV P l → p ∈ l → P p.2 := by
  intro l
  induction l with
  | nil => intro p _ hm; cases hm
  | cons q tl ih =>
      intro p ha hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact ha.1
      · exact ih ha.2 hm'

/-! ## The insertion sort `toSchema` uses

    Its whole point is that this is provable and `Array.qsort` is not. -/

theorem insertSorted_perm {α : Type} (lt : α → α → Bool) (x : α) :
    ∀ l : List α, (insertSorted lt x l).Perm (x :: l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons y tl ih =>
      rw [insertSorted]
      by_cases h : lt x y = true
      · rw [if_pos h]
      · rw [if_neg h]
        exact (List.Perm.cons y ih).trans (List.Perm.swap x y tl)

theorem sortBy_perm {α : Type} (lt : α → α → Bool) :
    ∀ l : List α, (sortBy lt l).Perm l := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons x tl ih =>
      rw [sortBy]
      exact (insertSorted_perm lt x (sortBy lt tl)).trans (List.Perm.cons x ih)

/-- A key below the rest of a sorted list does not appear again in it. -/
theorem below_not_mem {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) {k : K} :
    ∀ {l : List (K × V)}, Below lt k l → k ∉ l.map Prod.fst := by
  intro l
  induction l with
  | nil => intro _ hm; cases hm
  | cons p tl ih =>
      intro hb hm
      have hb1 : lt k p.1 = true := hb.1
      rw [List.map_cons] at hm
      rcases List.mem_cons.mp hm with heq | hmem
      · rw [heq, ho.irrefl] at hb1; exact Bool.noConfusion hb1
      · exact ih hb.2 hmem

/-- Sorted by a strict order, so no key repeats. -/
theorem sortedBy_nodup {lt eqk : K → K → Bool} (ho : StrictOrder lt eqk) :
    ∀ l : List (K × V), SortedBy lt l → (l.map Prod.fst).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons p tl ih =>
      intro hs
      rw [List.map_cons, List.nodup_cons]
      exact ⟨below_not_mem ho hs.1, ih hs.2⟩

/-! ## What remains

    `mergeBy_assoc` -- and with it `infer_perm`. Commutativity above was a
    nested induction on the two lists, three cases per step; associativity is
    an induction on the sum of three lengths with the heads compared pairwise,
    so nine top-level cases rather than three, each reducing both sides before
    the inductive hypothesis applies.

    An alternative worth weighing first, because it would also supply the
    sortedness invariant nothing has yet needed: characterise `mergeBy` by its
    lookups -- `lookup k (mergeBy a b)` is `combine` applied to the two
    lookups -- prove `mergeBy` preserves sortedness, and prove two sorted
    lists with equal lookups are equal. Commutativity and associativity then
    both fall out of the corresponding facts about `Option`, which are
    immediate. It costs a sortedness invariant on the walk, which
    `insertBy` and `Tables.upsert` would have to be shown to preserve.

    Once either is in hand: discharge `StrictOrder` for `String`'s `<` (via
    `Std.lt_trichotomy`), then for `Path.lt` and `Ty.lt`, which are built on
    it; then `Obs.merge`, `TableObs.merge` and `Tables.merge` are commutative
    and associative field by field; then `foldl_perm` in `Proofs.Inference`
    closes `infer_perm`, given a lemma that `mapM` over permuted lists which
    both succeed yields permuted results. -/

end Tatami
