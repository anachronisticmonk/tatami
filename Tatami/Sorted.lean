namespace Tatami

/-! # Association lists kept in order

    Observations are accumulated in association lists: tables by path, members
    by name, types by their order. Two corpora that are permutations of one
    another must produce the same tables, and an unordered list cannot manage
    that -- it records the order things were first seen, so two orders give two
    lists that differ only by rearrangement.

    Keeping them sorted makes merging commutative and associative *as a
    function*, so the equality the schema needs is ordinary equality rather
    than equality up to reordering. It also means nothing downstream has to
    sort, which matters because `Array.qsort` has no correctness lemmas in
    core: not even that it returns a permutation of its input.

    The order is passed in rather than taken from a class, because the two
    keys used here -- `Path` and `String` -- want different comparisons and
    neither wants an instance defined for it globally. -/

/-- Insert one entry, combining with what is already under that key.

    `combine old new` -- the accumulated value first, so that a `combine` that
    is not commutative still reads in observation order. -/
def insertBy (lt : K → K → Bool) (eqk : K → K → Bool) (combine : V → V → V)
    (k : K) (v : V) : List (K × V) → List (K × V)
  | [] => [(k, v)]
  | (k', v') :: tl =>
      if eqk k k' then (k', combine v' v) :: tl
      else if lt k k' then (k, v) :: (k', v') :: tl
      else (k', v') :: insertBy lt eqk combine k v tl

/-- Merge two ordered lists. Commutative and associative whenever `combine` is
    and `lt` is a strict total order, which is what makes the fold over a
    corpus independent of the order documents arrive in. -/
def mergeBy (lt : K → K → Bool) (eqk : K → K → Bool) (combine : V → V → V) :
    List (K × V) → List (K × V) → List (K × V)
  | [], b => b
  | a, [] => a
  | (ka, va) :: as, (kb, vb) :: bs =>
      if eqk ka kb then (ka, combine va vb) :: mergeBy lt eqk combine as bs
      else if lt ka kb then (ka, va) :: mergeBy lt eqk combine as ((kb, vb) :: bs)
      else (kb, vb) :: mergeBy lt eqk combine ((ka, va) :: as) bs
termination_by a b => a.length + b.length

/-- A sorted set: the same merge with no values to combine. -/
def unionBy (lt : K → K → Bool) (eqk : K → K → Bool) : List K → List K → List K
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs =>
      if eqk a b then a :: unionBy lt eqk as bs
      else if lt a b then a :: unionBy lt eqk as (b :: bs)
      else b :: unionBy lt eqk (a :: as) bs
termination_by a b => a.length + b.length

def insertSet (lt : K → K → Bool) (eqk : K → K → Bool) (x : K) : List K → List K
  | [] => [x]
  | y :: tl =>
      if eqk x y then y :: tl
      else if lt x y then x :: y :: tl
      else y :: insertSet lt eqk x tl

/-- Insertion sort, used where a proof has to be able to say what the result
    is. `Array.qsort` is faster, but core proves nothing about it -- not even
    that it returns a permutation of its input -- so a schema sorted with it
    cannot be shown to still have one table per path.

    Where the comparison is a strict total order on the elements, as it is
    everywhere this is used, the sorted list is unique and this agrees with
    `qsort` on every input. -/
def insertSorted (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: tl => if lt x y then x :: y :: tl else y :: insertSorted lt x tl

def sortBy (lt : α → α → Bool) : List α → List α
  | [] => []
  | x :: tl => insertSorted lt x (sortBy lt tl)

end Tatami
