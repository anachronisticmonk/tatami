import Proofs.Tree
import Proofs.Inference

/-!
# What Tatami guarantees

One theorem, to be read as the summary of everything else: given a corpus the
reader accepted and a generator run that succeeded, these eight things hold of
the output. Each conjunct is proved elsewhere; this file only puts them in one
place so that the guarantee can be stated without reading nine files.

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

/-- **The guarantee.** For a corpus that inference accepted and a schema the
    generator accepted:

    1. the emitted signature is well formed -- no module, value or record
       field name repeats;
    2. the schema is a property of the corpus and not of the order its
       documents arrived in;
    3. every collection edge the documents induce is declared in the
       signatures, and 4. every reference edge is too;
    5. and 6. conversely, every edge a reader finds between two tables is one
       the documents induced -- so nothing is invented;
    7. distinct tables get distinct module names, which is what makes 3--6 an
       isomorphism of trees rather than a collapse of one onto a smaller one;
    8. every table is reachable from the root, so walking the signatures from
       the root module enumerates the whole schema;
    9. and each member's type admits every type ever seen there, and is the
       least type that does. -/
theorem tatami_guarantees (cfg : Config) (nm : Naming) (ds : List Doc)
    (ts : Tables) (f : File)
    (hinf : inferCorpus cfg ds = .ok ts)
    (hgen : gen nm (toSchema ts) = .ok f) :
    -- 1. the signature compiles, as far as names go
    f.WellFormed
    -- 2. order-independence
  ∧ (∀ es ts', ds.Perm es → inferCorpus cfg es = .ok ts' → ts = ts')
    -- 3, 4. nothing in the document's tree is lost
  ∧ (∀ p q, CollEdge (toSchema ts) p q →
        FileCollEdge f (moduleName nm p) (moduleName nm q))
  ∧ (∀ p q, RefEdge (toSchema ts) p q →
        FileRefEdge f (moduleName nm p) (moduleName nm q))
    -- 5, 6. and nothing is invented
  ∧ (∀ t u, t ∈ toSchema ts → u ∈ toSchema ts →
        FileCollEdge f (moduleName nm t.path) (moduleName nm u.path) →
        CollEdge (toSchema ts) t.path u.path)
  ∧ (∀ t u, t ∈ toSchema ts → u ∈ toSchema ts →
        FileRefEdge f (moduleName nm t.path) (moduleName nm u.path) →
        RefEdge (toSchema ts) t.path u.path)
    -- 7. it is the same tree, not a quotient of it
  ∧ (∀ t u, t ∈ toSchema ts → u ∈ toSchema ts →
        moduleName nm t.path = moduleName nm u.path → t.path = u.path)
    -- 8. and it is rooted
  ∧ Rooted (toSchema ts)
    -- 9. the types are tight
  ∧ (∀ p t, (p, t) ∈ ts → ∀ k o, (k, o) ∈ t.members → ∀ τ, o.joined = some τ →
        (∀ ty, ty ∈ o.seen → ty ⊑ τ) ∧ (∀ σ, (∀ ty, ty ∈ o.seen → ty ⊑ σ) → τ ⊑ σ)) := by
  refine ⟨gen_wellFormed nm (toSchema ts) f hgen,
          fun es ts' hperm hinf' => infer_perm cfg ds es hperm hinf hinf',
          (gen_tree_complete nm (toSchema ts) f hgen).1,
          (gen_tree_complete nm (toSchema ts) f hgen).2,
          (gen_tree_sound nm (toSchema ts) f hgen).1,
          (gen_tree_sound nm (toSchema ts) f hgen).2,
          gen_moduleName_injOn nm (toSchema ts) f hgen,
          gen_rooted nm (toSchema ts) f hgen, ?_⟩
  intro p t hpt k o hko τ hτ
  exact ⟨infer_admits cfg ds ts hinf p t hpt k o hko τ hτ,
         fun σ hσ => infer_least cfg ds ts hinf p t hpt k o hko τ σ hτ hσ⟩

end Tatami
