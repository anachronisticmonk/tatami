import Proofs.Sorted
import Tatami.Infer

/-!
# The three orders the merges run on

`Proofs.Sorted` takes the key order as a hypothesis. These discharge it for
the three keys actually used: member names are `String`s, tables are keyed by
`Path`, and the set of types seen at a member is ordered by `Ty.lt`.

`Path` and `Ty` are both built on `String`'s order, so that is where it
starts.
-/

namespace Tatami

/-! ## Strings -/

theorem strOrder : StrictOrder (fun a b : String => decide (a < b)) (· == ·) where
  eq_iff a b := by simp
  asymm a b h := by
    simp only [decide_eq_true_eq] at h
    simp only [decide_eq_false_iff_not]
    intro hba
    exact String.lt_irrefl a (String.lt_trans h hba)
  total a b hne := by
    simp only [decide_eq_true_eq]
    rcases Std.lt_trichotomy a b with h | h | h
    · exact Or.inl h
    · exact absurd h hne
    · exact Or.inr h
  trans a b c hab hbc := by
    simp only [decide_eq_true_eq] at *
    exact String.lt_trans hab hbc

/-! ## Segments, and then paths -/

theorem segOrder : StrictOrder Seg.lt (· == ·) where
  eq_iff a b := by simp
  asymm a b h := by
    cases a <;> cases b <;>
      simp_all [Seg.lt, Seg.rank] <;>
      exact fun hba => String.lt_irrefl _ (String.lt_trans h hba)
  total a b hne := by
    cases a with
    | member x =>
        cases b with
        | member y =>
            simp only [Seg.lt]
            rcases Std.lt_trichotomy x y with h | h | h
            · exact Or.inl (by simpa using h)
            · exact absurd (by rw [h]) hne
            · exact Or.inr (by simpa using h)
        | elem => exact Or.inl (by simp [Seg.lt, Seg.rank])
        | entry => exact Or.inl (by simp [Seg.lt, Seg.rank])
    | elem =>
        cases b with
        | member y => exact Or.inr (by simp [Seg.lt, Seg.rank])
        | elem => exact absurd rfl hne
        | entry => exact Or.inl (by simp [Seg.lt, Seg.rank])
    | entry =>
        cases b with
        | member y => exact Or.inr (by simp [Seg.lt, Seg.rank])
        | elem => exact Or.inr (by simp [Seg.lt, Seg.rank])
        | entry => exact absurd rfl hne
  trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;>
      simp_all [Seg.lt, Seg.rank] <;>
      exact String.lt_trans hab hbc

theorem pathOrder : StrictOrder Path.lt (· == ·) where
  eq_iff a b := by simp
  asymm a b := by
    induction a generalizing b with
    | nil => intro h; cases b <;> simp_all [Path.lt]
    | cons x as ih =>
        intro h
        cases b with
        | nil => simp [Path.lt] at h
        | cons y bs =>
            rw [Path.lt] at h ⊢
            by_cases hxy : (x == y) = true
            · have : x = y := eq_of_beq hxy
              subst this
              rw [if_pos hxy] at h
              rw [if_pos (by simp : (x == x) = true)]
              exact ih bs h
            · rw [if_neg hxy] at h
              have hyx : (y == x) = false := by
                cases hb : (y == x) with
                | true => rw [eq_of_beq hb] at hxy; simp at hxy
                | false => rfl
              rw [hyx]
              simp only [if_false, Bool.false_eq_true]
              exact segOrder.asymm x y h
  total a b := by
    induction a generalizing b with
    | nil =>
        intro hne
        cases b with
        | nil => exact absurd rfl hne
        | cons y bs => exact Or.inl (by simp [Path.lt])
    | cons x as ih =>
        intro hne
        cases b with
        | nil => exact Or.inr (by simp [Path.lt])
        | cons y bs =>
            by_cases hxy : x = y
            · subst hxy
              have hne' : as ≠ bs := fun h => hne (by rw [h])
              rcases ih bs hne' with h | h
              · exact Or.inl (by rw [Path.lt, if_pos (by simp : (x == x) = true)]; exact h)
              · exact Or.inr (by rw [Path.lt, if_pos (by simp : (x == x) = true)]; exact h)
            · have hb : (x == y) = false := by
                cases hbb : (x == y) with
                | true => exact absurd (eq_of_beq hbb) hxy
                | false => rfl
              have hb' : (y == x) = false := by
                cases hbb : (y == x) with
                | true => exact absurd (eq_of_beq hbb).symm hxy
                | false => rfl
              rcases segOrder.total x y hxy with h | h
              · exact Or.inl (by rw [Path.lt, hb]; simpa using h)
              · exact Or.inr (by rw [Path.lt, hb']; simpa using h)
  trans a b c := by
    induction a generalizing b c with
    | nil =>
        intro hab hbc
        cases b <;> cases c <;> simp_all [Path.lt]
    | cons x as ih =>
        intro hab hbc
        cases b with
        | nil => simp [Path.lt] at hab
        | cons y bs =>
            cases c with
            | nil => simp [Path.lt] at hbc
            | cons z cs =>
                rw [Path.lt] at hab hbc ⊢
                by_cases hxy : (x == y) = true
                · have hxy' : x = y := eq_of_beq hxy
                  subst hxy'
                  rw [if_pos hxy] at hab
                  by_cases hxz : (x == z) = true
                  · have : x = z := eq_of_beq hxz
                    subst this
                    rw [if_pos hxy] at hbc
                    rw [if_pos hxz]
                    exact ih bs cs hab hbc
                  · rw [if_neg hxz] at hbc ⊢
                    exact hbc
                · rw [if_neg hxy] at hab
                  by_cases hyz : (y == z) = true
                  · have : y = z := eq_of_beq hyz
                    subst this
                    rw [if_neg hxy]
                    exact hab
                  · rw [if_neg hyz] at hbc
                    have hxz : (x == z) = false := by
                      cases hb : (x == z) with
                      | true =>
                          have : x = z := eq_of_beq hb
                          subst this
                          exact absurd (segOrder.asymm x y hab) (by rw [hbc]; simp)
                      | false => rfl
                    rw [hxz]
                    simp only [if_false, Bool.false_eq_true]
                    exact segOrder.trans x y z hab hbc

/-! ## Types

    `Ty.lt` is `Ty.rank` except between two references or two collections,
    where it is the order on the paths they name. -/

theorem tyOrder : StrictOrder Ty.lt (· == ·) where
  eq_iff a b := by simp
  asymm a b h := by
    cases a <;> cases b <;>
      simp_all [Ty.lt, Ty.rank] <;>
      exact pathOrder.asymm _ _ h
  total a b hne := by
    cases a <;> cases b <;> simp_all [Ty.lt, Ty.rank] <;>
      exact pathOrder.total _ _ hne
  trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;>
      simp_all [Ty.lt, Ty.rank] <;>
      exact pathOrder.trans _ _ _ hab hbc

end Tatami
