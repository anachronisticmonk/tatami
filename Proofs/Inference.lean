import Tatami.Infer

/-!
# Inference

Everything here is blocked on `Tatami.observeObject` being `partial`. Lean
cannot see that a member of an object is smaller than the object holding it,
so the recursion is not structural; a `partial` definition has no equations to
reason from, and none of the statements below can even be unfolded.

Making it total needs a size measure on `Doc` and the lemma that a member is
smaller than the object it sits in. That became possible once the reader
stopped handing back a tree map, and is the next thing to do here.

The statements are written down now so that the shape of what is wanted is
fixed before the work starts.
-/

namespace Tatami

/-- The schema is a property of the corpus, not of the order its documents
    arrived in. This is what makes "the schema" a meaningful phrase, and it
    rests on the join being commutative, associative and idempotent. -/
theorem infer_perm (cfg : Config) (ds es : List Doc) (h : ds.Perm es) :
    inferCorpus cfg ds = inferCorpus cfg es := by
  sorry

/-- The schema does not lie about the corpus: every value observed at a member
    fits the type that member was given. -/
theorem infer_admits (cfg : Config) (ds : List Doc) (ts : Tables)
    (h : inferCorpus cfg ds = .ok ts) :
    True := by
  sorry

/-- The type given to a member is the least one admitting every value observed
    there -- nothing is widened further than the data forces. Depends on
    `join_least`. -/
theorem infer_least (cfg : Config) (ds : List Doc) (ts : Tables)
    (h : inferCorpus cfg ds = .ok ts) :
    True := by
  sorry

end Tatami
