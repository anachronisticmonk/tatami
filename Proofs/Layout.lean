import Tatami.Gen

/-!
# Every member becomes a column

The design note's first correspondence: a member of the document becomes a
field of the record. `layoutOf` is where that happens, and this file says it
holds -- with the two exceptions the implementation makes and the prose
around it does not state precisely.

* A member named `id` is consumed as the table's key rather than becoming a
  field of its own.
* A member holding a collection contributes no field at all. The elements
  carry the key back instead, so there is nothing for the parent to hold.

Everything else appears, under its mangled name, at the type inference gave
it, optional exactly when the member was ever missing or null.

The loop in `layoutOf` only ever `yield`s and only ever appends, which is
what makes this an induction rather than a development: once a column is in
the accumulator nothing can remove it.
-/

namespace Tatami

/-- The body of `layoutOf`'s loop, named so it can be inducted over. -/
private def layoutStep (generated : List String) (c : Column) (cols : List Col) :
    Except Error (ForInStep (List Col)) :=
  if (c.name == "id") = true then pure (.yield cols)
  else
    let name := mangle c.name
    if generated.contains name = true then throw (Error.reservedColumnName c.name name)
    else match c.field.ty with
      | .coll _ => pure (.yield cols)
      | ty => pure (.yield (cols ++
          [{ name := name, ty := ty, nullable := c.field.nullable, kind := .member c.name }]))

/-- The accumulator only grows: nothing already laid out is lost. -/
private theorem layout_loop_grows (generated : List String) :
    ∀ (cs : List Column) (acc out : List Col),
      forIn cs acc (layoutStep generated) = .ok out → ∀ x ∈ acc, x ∈ out := by
  intro cs
  induction cs with
  | nil =>
      intro acc out h x hx
      simp only [List.forIn_nil] at h
      have he : acc = out := by injection h
      exact he ▸ hx
  | cons c tl ih =>
      intro acc out h x hx
      simp only [List.forIn_cons, layoutStep] at h
      split at h
      · exact ih _ _ (by simpa using h) x hx
      · split at h
        · injection h
        · split at h
          · exact ih _ _ (by simpa using h) x hx
          · exact ih _ _ (by simpa using h) x (by simp [hx])

/-- Every eligible member of the list reaches the output. -/
private theorem layout_loop_mem (generated : List String) :
    ∀ (cs : List Column) (acc out : List Col),
      forIn cs acc (layoutStep generated) = .ok out →
      ∀ c ∈ cs, c.name ≠ "id" → (∀ p, c.field.ty ≠ .coll p) →
        ({ name := mangle c.name, ty := c.field.ty
         , nullable := c.field.nullable, kind := .member c.name } : Col) ∈ out := by
  intro cs
  induction cs with
  | nil => intro _ _ _ c hc; simp at hc
  | cons d tl ih =>
      intro acc out h c hc hid hcoll
      simp only [List.forIn_cons, layoutStep] at h
      rcases List.mem_cons.mp hc with rfl | hct
      · -- the head is the member we are after, so this step appends it
        rw [if_neg (by simpa using hid)] at h
        split at h
        · injection h
        · split at h
          · next hty => exact absurd hty (hcoll _)
          · exact layout_loop_grows generated tl _ out (by simpa using h) _ (by simp)
      · -- it is further down the list
        split at h
        · exact ih _ _ (by simpa using h) c hct hid hcoll
        · split at h
          · injection h
          · split at h
            · exact ih _ _ (by simpa using h) c hct hid hcoll
            · exact ih _ _ (by simpa using h) c hct hid hcoll

/-- **Every member becomes a column.** A member of the document that is
    neither the table's key nor a collection appears in the layout, under its
    mangled name, at the type inference gave it, optional exactly when the
    member was ever missing or null. -/
theorem mem_layoutOf {nm : Naming} {t : Table} {cols : List Col} {c : Column}
    (h : layoutOf nm t = .ok cols)
    (hmem : c ∈ t.columns)
    (hid : c.name ≠ "id")
    (hcoll : ∀ p, c.field.ty ≠ .coll p) :
    ({ name := mangle c.name, ty := c.field.ty
     , nullable := c.field.nullable, kind := .member c.name } : Col) ∈ cols := by
  unfold layoutOf at h
  cases hk : keyTyOf t with
  | error e => rw [hk] at h; injection h
  | ok keyTy =>
      rw [hk] at h
      simp only [bind_pure] at h
      split at h <;>
        exact layout_loop_mem _ _ _ _ h c hmem hid hcoll

end Tatami
