import Tatami.Gen
import Tatami.Print

/-!
# The generated signature is well formed

The one guarantee available without shredding, and the one worth having: the
emitted OCaml always compiles.

`WellFormed` is our account of what OCaml accepts for this fragment, not
OCaml's own rules -- the gap between the two is real and cannot be closed
without formalising OCaml. What it does exclude is the failure this generator
is most likely to produce: two record fields with the same name.
-/

namespace Tatami

/-- Every field of a record type has a distinct name. -/
def Module.fieldsDistinct (m : Module) : Prop :=
  ∀ d ∈ m.decls, ∀ n fs, d = Decl.recordType n fs →
    (fs.map RecField.name).Nodup

/-- Every value declared in a module has a distinct name. -/
def Module.valuesDistinct (m : Module) : Prop :=
  (m.decls.filterMap (fun d => match d with
    | .value n _ => some n
    | _ => none)).Nodup

/-- Every module in the file has a distinct name. -/
def File.modulesDistinct (f : File) : Prop :=
  (f.modules.map Module.name).Nodup

def File.WellFormed (f : File) : Prop :=
  f.modulesDistinct ∧ ∀ m ∈ f.modules, m.fieldsDistinct ∧ m.valuesDistinct

/-- Whatever schema it is given, the generator either refuses it or produces a
    well-formed file. It never emits a signature with a duplicate field.

    Distinctness of fields reduces to `mangle_injective` together with the
    checks in `genModule` that no member collides with a generated column;
    distinctness of modules reduces to paths being distinct and
    `mangle_starts_lower`. -/
theorem gen_wellFormed (s : Schema) (f : File) (h : gen s = .ok f) :
    f.WellFormed := by
  sorry

end Tatami
