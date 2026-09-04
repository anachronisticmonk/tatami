import Tatami.Ty

/-!
# The type order

Inference gives a member one type, however many values were observed there,
by joining the observations. Three facts make that well defined:

* the join does not depend on the order two observations are combined in
  (commutativity and associativity), so the schema does not depend on the
  order documents arrive in;
* joining a type with itself changes nothing (idempotence), so a member seen
  twice with the same type is no different from one seen once;
* the join is the *least* type above both, so nothing is widened further than
  the data forces.

`Ty` has few constructors, so most of these are exhaustive case analysis.
-/

namespace Tatami

/-- One type is below another when joining them gives the second. -/
def Ty.le (a b : Ty) : Prop := Ty.join a b = some b

infix:50 " ⊑ " => Ty.le

theorem join_comm (a b : Ty) : Ty.join a b = Ty.join b a := by
  cases a <;> cases b <;> simp [Ty.join] <;>
    · rename_i p q
      by_cases h : p = q
      · subst h; simp
      · simp [h, Ne.symm h]

theorem join_idem (a : Ty) : Ty.join a a = some a := by
  cases a <;> simp [Ty.join]

theorem bot_le (a : Ty) : Ty.bot ⊑ a := by
  cases a <;> rfl

/-- The join is above its left argument, and by commutativity above both. -/
theorem le_join_left {a b c : Ty} (h : Ty.join a b = some c) : a ⊑ c := by
  unfold Ty.le
  cases a <;> cases b <;> simp only [Ty.join] at h ⊢
  all_goals
    first
      | (cases h; simp)
      | (split at h <;> first | (cases h; simp [Ty.join]) | simp_all [Ty.join])
      | simp_all [Ty.join]

theorem le_join_right {a b c : Ty} (h : Ty.join a b = some c) : b ⊑ c := by
  rw [join_comm] at h
  exact le_join_left h

/-- Nothing above both is below the join: the join is the least upper bound.

    This is the property that makes an inferred type the tightest one the data
    admits, rather than merely one that fits. -/
theorem join_least {a b c d : Ty} (h : Ty.join a b = some c) (ha : a ⊑ d) (hb : b ⊑ d) :
    c ⊑ d := by
  sorry

/-- The join is associative where both sides are defined, so folding a list of
    observations gives the same answer whatever order it is folded in. -/
theorem join_assoc (a b c : Ty) :
    (Ty.join a b).bind (fun ab => Ty.join ab c)
      = (Ty.join b c).bind (fun bc => Ty.join a bc) := by
  sorry

end Tatami
