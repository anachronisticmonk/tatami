import Proofs.Tree
import Proofs.Inference
import Proofs.Counts

/-!
# What Tatami guarantees

One theorem, `pipeline_correct`, in five named parts: given a corpus the
reader accepted and a generator run that succeeded, the emitted signature is
well formed, the schema is canonical, the document's structure is preserved,
the inferred types are principal, and a column is optional exactly when the
data made it so. Each part is proved elsewhere; this file
groups them so the guarantee can be stated without reading nine files.

The four names are the standard ones. *Canonicity* because the output is a
canonical form -- equal content gives an equal answer, not merely an
equivalent one. *Adequacy* and *minimality* because a type that admits every
value seen is adequate and one that admits no more is minimal, and the two
together are what makes an inferred type **principal**; `Proofs.Inference`
already uses those words. *Structure preservation* rather than "faithful",
which in category theory means something narrower than what is proved here.

Two things it deliberately does *not* say.

It says nothing about a corpus the program refuses. Every conjunct is
conditional on `inferCorpus` and `gen` both returning `ok`, and both refuse
inputs -- a member holding two types with no common type, a schema whose tree
a signature cannot express. The guarantee is about what is emitted, not about
what is accepted.

And it says nothing about rows. The program emits a description of tables; the
loader that fills them is OCaml, outside what Lean sees here. A preservation
theorem would need the shredder first.
-/

namespace Tatami

/-! ## The four parts -/

/-- **Well-formedness.** The emitted signature repeats no module name, no
    value name within a module, and no field name within a record. This is
    what "the output is a legal OCaml signature" amounts to for this fragment,
    and it holds of every schema because `gen` checks its own output. -/
theorem signature_wellFormed (nm : Naming) (s : Schema) (f : File)
    (hgen : gen nm s = .ok f) : f.WellFormed :=
  gen_wellFormed nm s f hgen

/-- **Canonicity.** The schema is determined by the corpus as a collection of
    documents, not by the order they arrived in. Shuffle the corpus and the
    answer is *equal*, not merely equivalent -- which is what makes two runs
    of the generator agree byte for byte. -/
theorem schema_canonical (cfg : Config) (ds : List Doc) (ts : Tables)
    (hinf : inferCorpus cfg ds = .ok ts) :
    ∀ es ts', ds.Perm es → inferCorpus cfg es = .ok ts' → ts = ts' :=
  fun es ts' hperm hinf' => infer_perm cfg ds es hperm hinf hinf'

/-- **Structure preservation.** The tree the documents induce and the graph a
    reader finds in the generated signatures are the same graph.

    Six clauses, and each is needed. The first two say no edge is lost, the
    next two that none is invented; together they make the edge sets agree.
    The fifth says distinct tables get distinct modules, which is what lifts
    that agreement from "the same edges" to "the same graph" rather than a
    collapse of one onto a smaller one. The sixth says the graph is rooted, so
    walking it from the root module reaches everything -- without it a table
    could be declared and never reachable, which is a table the loader would
    create and never fill. -/
theorem structure_preserved (nm : Naming) (s : Schema) (f : File)
    (hgen : gen nm s = .ok f) :
    -- nothing lost
    (∀ p q, CollEdge s p q → FileCollEdge f (moduleName nm p) (moduleName nm q))
  ∧ (∀ p q, RefEdge s p q → FileRefEdge f (moduleName nm p) (moduleName nm q))
    -- nothing invented
  ∧ (∀ t u, t ∈ s → u ∈ s →
        FileCollEdge f (moduleName nm t.path) (moduleName nm u.path) →
        CollEdge s t.path u.path)
  ∧ (∀ t u, t ∈ s → u ∈ s →
        FileRefEdge f (moduleName nm t.path) (moduleName nm u.path) →
        RefEdge s t.path u.path)
    -- the same graph, not a quotient of it
  ∧ (∀ t u, t ∈ s → u ∈ s →
        moduleName nm t.path = moduleName nm u.path → t.path = u.path)
    -- and rooted
  ∧ Rooted s :=
  ⟨(gen_tree_complete nm s f hgen).1, (gen_tree_complete nm s f hgen).2,
   (gen_tree_sound nm s f hgen).1, (gen_tree_sound nm s f hgen).2,
   gen_moduleName_injOn nm s f hgen, gen_rooted nm s f hgen⟩

/-- **Principality.** Each member is given the principal type of the values
    seen there: one that admits every one of them (*adequacy*), and the least
    type that does (*minimality*).

    Adequacy alone is nearly free -- a corpus of integers is adequately
    described by `float`, or by `int option`. Minimality is what rules the
    loose answers out, and the two together pin the type from both sides. -/
theorem types_principal (cfg : Config) (ds : List Doc) (ts : Tables)
    (hinf : inferCorpus cfg ds = .ok ts) :
    ∀ p t, (p, t) ∈ ts → ∀ k o, (k, o) ∈ t.members → ∀ τ, o.joined = some τ →
      (∀ ty, ty ∈ o.seen → ty ⊑ τ) ∧ (∀ σ, (∀ ty, ty ∈ o.seen → ty ⊑ σ) → τ ⊑ σ) := by
  intro p t hpt k o hko τ hτ
  exact ⟨infer_admits cfg ds ts hinf p t hpt k o hko τ hτ,
         fun σ hσ => infer_least cfg ds ts hinf p t hpt k o hko τ σ hτ hσ⟩

/-- **Nullability.** A column is optional exactly when some document lacked a
    value there.

    Two halves. The counts identity says every visit to a table is accounted
    for at each of its members: a value, an explicit `null`, or an absence,
    and nothing else. That matters because `inferFinish` computes absence by
    *truncating* subtraction -- without the identity a member some document
    had omitted could report `absent = 0`, come out non-optional, and the
    generator would emit `string` where the data needs `string option`. The
    emitted OCaml would compile and then fail on the first document missing
    that member, with nothing to say what went wrong.

    The second half reads the flag off the identity: `nullable` is set
    precisely when the member carried a value in fewer than all of its table's
    visits. So the `option` is neither missing nor gratuitous.

    Together with `types_principal` this is the whole of what a generated
    field declaration claims: that pins the type from both sides, this pins
    the `option` from both sides. -/
theorem nullability_sound (cfg : Config) (ds : List Doc) (ts : Tables)
    (hinf : inferCorpus cfg ds = .ok ts) :
    ∀ p t, (p, t) ∈ ts → ∀ k o, (k, o) ∈ t.members →
      o.values + o.nulls + o.absent = t.visits
      ∧ (o.nullable = true ↔ o.values < t.visits) := by
  intro p t hpt k o hko
  have hc := infer_counts cfg ds ts hinf p t hpt k o hko
  refine ⟨hc, ?_⟩
  unfold Obs.nullable
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

/-! ## And the whole -/

/-- **Correctness of the pipeline.** For a corpus inference accepted and a
    schema the generator accepted: the signature is well formed, the schema is
    canonical, the document's structure is preserved, the types are principal,
    and a column is optional exactly when the data made it so.

    What it does not say. Every part is conditional on both stages returning
    `ok`, and both refuse inputs -- a member holding two types with no common
    type, a schema whose tree a signature cannot express. The guarantee is
    about what is emitted, not about what is accepted. And it says nothing
    about rows: the program emits a description of tables, and the loader that
    fills them is OCaml, outside what Lean sees here. -/
theorem pipeline_correct (cfg : Config) (nm : Naming) (ds : List Doc)
    (ts : Tables) (f : File)
    (hinf : inferCorpus cfg ds = .ok ts)
    (hgen : gen nm (toSchema ts) = .ok f) :
    f.WellFormed
  ∧ (∀ es ts', ds.Perm es → inferCorpus cfg es = .ok ts' → ts = ts')
  ∧ ((∀ p q, CollEdge (toSchema ts) p q →
        FileCollEdge f (moduleName nm p) (moduleName nm q))
     ∧ (∀ p q, RefEdge (toSchema ts) p q →
        FileRefEdge f (moduleName nm p) (moduleName nm q))
     ∧ (∀ t u, t ∈ toSchema ts → u ∈ toSchema ts →
          FileCollEdge f (moduleName nm t.path) (moduleName nm u.path) →
          CollEdge (toSchema ts) t.path u.path)
     ∧ (∀ t u, t ∈ toSchema ts → u ∈ toSchema ts →
          FileRefEdge f (moduleName nm t.path) (moduleName nm u.path) →
          RefEdge (toSchema ts) t.path u.path)
     ∧ (∀ t u, t ∈ toSchema ts → u ∈ toSchema ts →
          moduleName nm t.path = moduleName nm u.path → t.path = u.path)
     ∧ Rooted (toSchema ts))
  ∧ (∀ p t, (p, t) ∈ ts → ∀ k o, (k, o) ∈ t.members → ∀ τ, o.joined = some τ →
        (∀ ty, ty ∈ o.seen → ty ⊑ τ) ∧ (∀ σ, (∀ ty, ty ∈ o.seen → ty ⊑ σ) → τ ⊑ σ))
  ∧ (∀ p t, (p, t) ∈ ts → ∀ k o, (k, o) ∈ t.members →
        o.values + o.nulls + o.absent = t.visits
        ∧ (o.nullable = true ↔ o.values < t.visits)) :=
  ⟨signature_wellFormed nm (toSchema ts) f hgen,
   schema_canonical cfg ds ts hinf,
   structure_preserved nm (toSchema ts) f hgen,
   types_principal cfg ds ts hinf,
   nullability_sound cfg ds ts hinf⟩

end Tatami
