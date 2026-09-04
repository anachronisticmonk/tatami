import Tatami.Mangle

/-!
# Names

`mangle` turns a JSON member name into an OCaml identifier. Everything rests
on it being injective: two distinct members must never become one column, and
two distinct tables must never become one module.
-/

namespace Tatami

/-- Distinct member names give distinct identifiers.

    The scheme escapes every byte outside `[A-Za-z0-9']` as `_` followed by
    two hex digits, `_` itself included, which is what makes `_` an
    unambiguous escape introducer. The prefix and keyword-suffix rules must
    not undo that. -/
theorem mangle_injective {a b : String} (h : mangle a = mangle b) : a = b := by
  sorry

/-- A mangled name always begins with a lowercase letter, which is what makes
    capitalising one character injective, and so module names distinct. -/
theorem mangle_starts_lower (s : String) :
    ∃ c t, mangle s = String.ofList (c :: t) ∧ 'a' ≤ c ∧ c ≤ 'z' := by
  sorry

end Tatami
