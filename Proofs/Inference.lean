import Tatami.Infer
import Proofs.Lattice
import Proofs.Walk
import Proofs.Spec

/-!
# Inference

## What changed, and why

`infer_perm` used to be a large induction waiting to happen, blocked twice
over: the accumulator recorded discovery order, so two orderings gave lists
that differed by rearrangement rather than being equal; and `toSchema` sorted
with `Array.qsort`, which has no correctness lemmas in core -- not even that
it returns a permutation -- so sorting could not be used to normalise.

Rather than prove around that, the inference was restructured so the property
holds by construction:

* each document is observed from nothing, and the results are **merged**
  rather than threaded through a shared accumulator;
* the merge is commutative and associative in every field -- counts add, type
  sets union, flags disjoin -- so the order documents arrive in cannot matter;
* tables, members and the types seen at a member are kept **in order**, so the
  merge is commutative *as a function* and the result is canonical. Nothing
  downstream needs to sort, and `qsort` stops being in the way.

`Obs` now holds the **set** of types seen at a member rather than their
running join. Union of sets needs no proof to be commutative, the join is
taken once at the end, and a conflict can name every type involved instead of
the two that happened to meet first.

## Where that leaves the three statements

`infer_perm` is now an equality of `Tables`, not of schemas: the tables are
canonical, so there is nothing left for `toSchema` to normalise. What remains
is a chain of small lemmas rather than an induction through the walk --
`mergeBy` commutative and associative given a strict total order on keys and a
commutative associative combine, then that discharged for `String`, `Path` and
`Ty`, then `foldl_perm` below. `Std.lt_trichotomy` supplies the order facts
for `String`; `Path.lt` and `Ty.lt` are built on it.

`infer_admits` and `infer_least` are proved. With `seen` holding the observed
types as data, "the column's type is an upper bound of what was seen" and "it
is the least such" became statements about `Obs.joined` and `Obs.seen`,
discharged from `le_join_left` and `join_least` -- rather than needing a
conformance relation invented from nothing. Both are properties of the fold
alone, so neither proof uses its `inferCorpus` hypothesis; it is kept so the
statement reads as a fact about an inferred schema.

What they do *not* cover is nullability. `Obs.nullable` is derived from the
`nulls` and `absent` counts; `Proofs.Counts` proves those add up to the visit
count, which is what makes `absent` meaningful, but nothing yet connects it
back to the documents that omitted the key.
-/

namespace Tatami

/-- A fold over a permuted list gives the same answer when the step function
    commutes in its list argument. The swap case is the whole content, and it
    is where `Tables.merge` being commutative will be used. -/
theorem foldl_perm {α β : Type} {f : β → α → β}
    (hrc : ∀ b x y, f (f b x) y = f (f b y) x) :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → ∀ b, l₁.foldl f b = l₂.foldl f b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro b; rfl
  | cons x _ ih => intro b; simpa [List.foldl] using ih (f b x)
  | swap x y l => intro b; simp only [List.foldl]; rw [hrc]
  | trans _ _ ih₁ ih₂ => intro b; rw [ih₁, ih₂]

/-- The schema is a property of the corpus, not of the order its documents
    arrived in. Now an equality of `Tables`: they are kept canonical, so there
    is nothing for `toSchema` to normalise and `toSchema ta = toSchema tb`
    follows by congruence.

    Conditional on success because *which* error is reported first does depend
    on order -- if one document has a duplicate member and another a nested
    array, the answer differs. Whether inference succeeds does not. -/
theorem mapM_ok_of_all {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α}, (∀ x, x ∈ l → ∃ b, f x = .ok b) → ∃ r, l.mapM f = .ok r := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons a as ih =>
      intro hall
      obtain ⟨b, hb⟩ := hall a (List.mem_cons_self ..)
      obtain ⟨r, hr⟩ := ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      exact ⟨b :: r, by rw [List.mapM_cons, hb, hr]; rfl⟩

/-- Permuted inputs give permuted outputs, when both succeed. -/
theorem mapM_perm {α β ε : Type} {f : α → Except ε β} :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → ∀ {r₁ r₂ : List β},
      l₁.mapM f = .ok r₁ → l₂.mapM f = .ok r₂ → r₁.Perm r₂ := by
  intro l₁ l₂ hp
  induction hp with
  | nil =>
      intro r₁ r₂ h1 h2
      rw [List.mapM_nil] at h1 h2; cases h1; cases h2; exact List.Perm.refl []
  | cons x _ ih =>
      intro r₁ r₂ h1 h2
      rw [List.mapM_cons] at h1 h2
      obtain ⟨b1, hb1, k1⟩ := except_bind_ok h1
      obtain ⟨s1, hs1, e1⟩ := except_bind_ok k1
      obtain ⟨b2, hb2, k2⟩ := except_bind_ok h2
      obtain ⟨s2, hs2, e2⟩ := except_bind_ok k2
      cases e1; cases e2
      rw [hb1] at hb2; cases hb2
      exact List.Perm.cons _ (ih hs1 hs2)
  | swap x y l =>
      intro r₁ r₂ h1 h2
      rw [List.mapM_cons, List.mapM_cons] at h1
      rw [List.mapM_cons, List.mapM_cons] at h2
      obtain ⟨by1, hby1, a1⟩ := except_bind_ok h1
      obtain ⟨s1, hs1, e1⟩ := except_bind_ok a1
      obtain ⟨bx1, hbx1, b1⟩ := except_bind_ok hs1
      obtain ⟨t1, ht1, f1⟩ := except_bind_ok b1
      obtain ⟨bx2, hbx2, a2⟩ := except_bind_ok h2
      obtain ⟨s2, hs2, e2⟩ := except_bind_ok a2
      obtain ⟨by2, hby2, b2⟩ := except_bind_ok hs2
      obtain ⟨t2, ht2, f2⟩ := except_bind_ok b2
      cases e1; cases e2; cases f1; cases f2
      rw [hby1] at hby2; cases hby2
      rw [hbx1] at hbx2; cases hbx2
      rw [ht1] at ht2; cases ht2
      exact List.Perm.swap _ _ _
  | trans hab _ ih₁ ih₂ =>
      intro r₁ r₂ h1 h2
      obtain ⟨rm, hm⟩ := mapM_ok_of_all (f := f) (fun x hx => by
        obtain ⟨b, _, hb⟩ := mapM_ok_pointwise h1 x (hab.mem_iff.mpr hx)
        exact ⟨b, hb⟩)
      exact List.Perm.trans (ih₁ h1 hm) (ih₂ hm h2)

/-- `foldl_perm` where the laws hold only of values satisfying a predicate,
    which is what `Tables.merge` needs: it commutes on observations kept in
    key order, and not otherwise. -/
theorem foldl_perm_on {α β : Type} {f : β → α → β} {P : β → Prop} {Q : α → Prop}
    (hP : ∀ b x, P b → Q x → P (f b x))
    (hrc : ∀ b x y, P b → Q x → Q y → f (f b x) y = f (f b y) x) :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → (∀ x, x ∈ l₁ → Q x) →
      ∀ b, P b → l₁.foldl f b = l₂.foldl f b := by
  intro l₁ l₂ hp
  induction hp with
  | nil => intro _ b _; rfl
  | cons x _ ih =>
      intro hq b hb
      simp only [List.foldl]
      exact ih (fun y hy => hq y (List.mem_cons_of_mem _ hy)) (f b x)
        (hP b x hb (hq x (List.mem_cons_self ..)))
  | swap x y l =>
      intro hq b hb
      simp only [List.foldl]
      rw [hrc b y x hb (hq y (by simp)) (hq x (by simp))]
  | trans hab _ ih₁ ih₂ =>
      intro hq b hb
      rw [ih₁ hq b hb, ih₂ (fun y hy => hq y (hab.mem_iff.mpr hy)) b hb]

theorem infer_perm (cfg : Config) (ds es : List Doc) (h : ds.Perm es)
    {ta tb : Tables} (hda : inferCorpus cfg ds = .ok ta)
    (hdb : inferCorpus cfg es = .ok tb) :
    ta = tb := by
  unfold inferCorpus at hda hdb
  obtain ⟨tssa, hma, hfa⟩ := except_bind_ok hda
  obtain ⟨tssb, hmb, hfb⟩ := except_bind_ok hdb
  -- the observations are a permutation of each other, and each is in order
  have hperm : tssa.Perm tssb := mapM_perm h hma hmb
  have hall : ∀ t, t ∈ tssa → TablesOk t := by
    intro t ht
    obtain ⟨d, _, hd⟩ := mem_of_mapM_ok hma t ht
    exact observeDocument_ok hd
  -- so the fold gives the same answer
  have hfold : tssa.foldl Tables.merge [] = tssb.foldl Tables.merge [] :=
    foldl_perm_on (P := TablesOk) (Q := TablesOk)
      (fun _ _ hb hx => Tables.merge_ok hb hx)
      (fun _ _ _ hb hx hy => Tables.merge_right_comm hb hx hy)
      hperm hall [] TablesOk.nil
  rw [hfold, hfb] at hfa
  exact (Except.ok.inj hfa).symm

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

/-! ## What a member's type says about what was seen there

    With `Obs.seen` holding the observed types as data rather than their
    running join, both of the remaining theorems are statements about
    `Obs.joined` -- a fold of `Ty.join` over that list -- rather than about
    the walk that collected it. That is what the restructure bought: they are
    now provable from `Proofs.Lattice` alone. -/

/- `le_trans`, which the fold below needs at every step, is in
   `Proofs.Lattice` with the rest of the order. -/

/-- Once the join is undefined it stays undefined, so a fold reaching `some`
    never passed through `none`. -/
theorem foldJoin_none (l : List Ty) :
    l.foldl (fun acc t => acc.bind (Ty.join · t)) none = none := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simpa using ih

/-- Every type folded in is below the result, and so is the starting point. -/
theorem foldJoin_le : ∀ {l : List Ty} {a τ : Ty},
    l.foldl (fun acc t => acc.bind (Ty.join · t)) (some a) = some τ →
    a ⊑ τ ∧ ∀ t, t ∈ l → t ⊑ τ := by
  intro l
  induction l with
  | nil =>
      intro a τ h
      simp only [List.foldl_nil, Option.some.injEq] at h
      subst h
      exact ⟨join_idem _, by intro t ht; cases ht⟩
  | cons x xs ih =>
      intro a τ h
      rw [List.foldl_cons] at h
      cases hax : Ty.join a x with
      | none =>
          rw [show ((some a).bind fun y => Ty.join y x) = Ty.join a x from rfl, hax,
              foldJoin_none] at h
          cases h
      | some m =>
          rw [show ((some a).bind fun y => Ty.join y x) = Ty.join a x from rfl, hax] at h
          obtain ⟨hm, hrest⟩ := ih h
          refine ⟨le_trans (le_join_left hax) hm, ?_⟩
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht'
          · exact le_trans (le_join_right hax) hm
          · exact hrest t ht'

/-- And the result is the least such type: anything above everything folded in
    is above the result. -/
theorem foldJoin_least : ∀ {l : List Ty} {a τ σ : Ty},
    l.foldl (fun acc t => acc.bind (Ty.join · t)) (some a) = some τ →
    a ⊑ σ → (∀ t, t ∈ l → t ⊑ σ) → τ ⊑ σ := by
  intro l
  induction l with
  | nil =>
      intro a τ σ h ha _
      simp only [List.foldl_nil, Option.some.injEq] at h
      subst h; exact ha
  | cons x xs ih =>
      intro a τ σ h ha hall
      rw [List.foldl_cons] at h
      cases hax : Ty.join a x with
      | none =>
          rw [show ((some a).bind fun y => Ty.join y x) = Ty.join a x from rfl, hax,
              foldJoin_none] at h
          cases h
      | some m =>
          rw [show ((some a).bind fun y => Ty.join y x) = Ty.join a x from rfl, hax] at h
          exact ih h (join_least hax ha (hall x (List.mem_cons_self ..)))
            (fun t ht => hall t (List.mem_cons_of_mem _ ht))

/-- The type a member is given admits every type ever seen there. -/
theorem obs_admits {o : Obs} {τ : Ty} (h : o.joined = some τ) :
    ∀ t, t ∈ o.seen → t ⊑ τ := (foldJoin_le h).2

/-- And it is the least such type: nothing is widened further than the data
    forces. -/
theorem obs_least {o : Obs} {τ σ : Ty} (h : o.joined = some τ)
    (hσ : ∀ t, t ∈ o.seen → t ⊑ σ) : τ ⊑ σ :=
  foldJoin_least h (bot_le σ) hσ

/-- The schema does not lie about the corpus: every value observed at a member
    fits the type that member was given.

    Stated of the member's `joined`, which `inferFinish` has already checked is
    `some` -- it refuses a corpus where any member's types have no common
    type, which is exactly the `none` case. -/
theorem infer_admits (cfg : Config) (ds : List Doc) (ts : Tables)
    (_h : inferCorpus cfg ds = .ok ts) :
    ∀ p t, (p, t) ∈ ts → ∀ k o, (k, o) ∈ t.members →
      ∀ τ, o.joined = some τ → ∀ ty, ty ∈ o.seen → ty ⊑ τ := by
  intro _ _ _ _ _ _ _ hj
  exact obs_admits hj

/-- The type given to a member is the least one admitting every value observed
    there -- nothing is widened further than the data forces. -/
theorem infer_least (cfg : Config) (ds : List Doc) (ts : Tables)
    (_h : inferCorpus cfg ds = .ok ts) :
    ∀ p t, (p, t) ∈ ts → ∀ k o, (k, o) ∈ t.members →
      ∀ τ σ, o.joined = some τ → (∀ ty, ty ∈ o.seen → ty ⊑ σ) → τ ⊑ σ := by
  intro _ _ _ _ _ _ _ _ hj hσ
  exact obs_least hj hσ

end Tatami
