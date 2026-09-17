import Tatami.Gen

/-!
# The generated signature is well formed

The one guarantee available without shredding, and the one worth having: the
emitted OCaml always compiles.

`WellFormed` is our account of what OCaml accepts for this fragment, not
OCaml's own rules -- the gap between the two is real and cannot be closed
without formalising OCaml. What it does exclude is the failure this generator
is most likely to produce: two record fields with the same name.

The proposition here is the reading; `File.okB` in `Tatami.Ocaml` is the same
condition as a `Bool`, which `gen` tests of its own output before returning
it. `okB_sound` connects the two, and `gen_wellFormed` follows.

**What this does not cover.** Nothing here constrains *references*: a
`qualified M n` naming a module that does not exist, or one compiled after
the unit that names it, is well formed by this definition and still does not
compile. Since each module became its own `.mli`, that second failure is the
live one: OCaml units cannot be mutually recursive, so `gen` puts every key
type in `Ids` to keep the references acyclic and `File.units` emits `Ids`
first, then deepest-first. Nothing here says that order is a topological sort
of the references actually emitted. Making "the emitted OCaml compiles" the
true reading of this theorem needs that, and a scoping clause.
-/

namespace Tatami

/-- Every field of a record type has a distinct name. -/
def Module.fieldsDistinct (m : Module) : Prop :=
  ∀ d ∈ m.decls, ∀ n fs, d = Decl.recordType n fs →
    (fs.map RecField.name).Nodup

/-- Every value declared in a module has a distinct name. -/
def Module.valuesDistinct (m : Module) : Prop :=
  m.valueNames.Nodup

/-- Every module in the file has a distinct name. -/
def File.modulesDistinct (f : File) : Prop :=
  (f.modules.map Module.name).Nodup

def File.WellFormed (f : File) : Prop :=
  f.modulesDistinct ∧ ∀ m ∈ f.modules, m.fieldsDistinct ∧ m.valuesDistinct

/-- The `Bool` check is not weaker than the proposition it stands for. This is
    the only place the two accounts meet; everything below goes through it. -/
theorem nodupNames_sound : ∀ {l : List String}, nodupNames l = true → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons n ns ih =>
      intro h
      simp only [nodupNames, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
                 Bool.not_true] at h
      refine List.nodup_cons.mpr ⟨?_, ih h.2⟩
      intro hmem
      have hc : ns.contains n = true := List.contains_iff_mem.mpr hmem
      rw [h.1] at hc
      simp at hc

theorem okB_sound {f : File} (h : f.okB = true) : f.WellFormed := by
  simp only [File.okB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hmods, hall⟩ := h
  refine ⟨nodupNames_sound hmods, fun m hm => ?_⟩
  have hmok := hall m hm
  simp only [Module.okB, Bool.and_eq_true, List.all_eq_true] at hmok
  obtain ⟨hfields, hvals⟩ := hmok
  refine ⟨?_, nodupNames_sound hvals⟩
  intro d hd n fs hdef
  refine nodupNames_sound (hfields _ ?_)
  exact List.mem_filterMap.mpr ⟨d, hd, by subst hdef; rfl⟩

theorem certify_wellFormed {f g : File} (h : certify f = .ok g) : g.WellFormed := by
  unfold certify at h
  split at h
  · next hb => cases h; exact okB_sound hb
  · exact absurd h (by simp)

/-- Whatever schema it is given, the generator either refuses it or produces a
    well-formed file. It never emits a signature with a duplicate field.

    The proof is by inversion on the check `gen` performs, not by tracking
    names through `genModule`. That is deliberate: it makes the theorem hold
    of every `Schema`, including ones inference would never build, and it
    does not depend on `mangle_injective`. -/
theorem gen_wellFormed (nm : Naming) (s : Schema) (f : File) (h : gen nm s = .ok f) :
    f.WellFormed := by
  unfold gen at h
  split at h
  · cases h
  · split at h
    · exact absurd h (by simp)
    · exact certify_wellFormed h

end Tatami
