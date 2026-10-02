import Proofs.Order

/-!
# The observation merges form a commutative monoid

`Tables.merge` is `mergeBy` over `TableObs.merge`, which is `mergeBy` over
`Obs.merge`, which is `unionBy` on the set of types seen and addition or
disjunction on everything else. Commutativity and associativity hold at each
level, given that the lists are kept in key order -- which is the invariant
the walk maintains and `TablesOk` below states.
-/

namespace Tatami

/-! ## The order invariant, level by level -/

def ObsOk (o : Obs) : Prop := SortedK Ty.lt o.seen

def TableObsOk (t : TableObs) : Prop :=
  SortedBy (fun a b : String => decide (a < b)) t.members ∧ AllV ObsOk t.members

def TablesOk (ts : Tables) : Prop :=
  SortedBy Path.lt ts ∧ AllV TableObsOk ts

/-! ## One member's observations -/

theorem Obs.merge_ok {a b : Obs} (ha : ObsOk a) (hb : ObsOk b) :
    ObsOk (Obs.merge a b) :=
  unionBy_sorted tyOrder _ _ ha hb

theorem Obs.merge_comm {a b : Obs} (_ha : ObsOk a) (_hb : ObsOk b) :
    Obs.merge a b = Obs.merge b a := by
  unfold Obs.merge
  rw [unionBy_comm tyOrder a.seen b.seen]
  simp [Nat.add_comm, Bool.or_comm]

theorem Obs.merge_assoc {a b c : Obs} (ha : ObsOk a) (hb : ObsOk b) (hc : ObsOk c) :
    Obs.merge (Obs.merge a b) c = Obs.merge a (Obs.merge b c) := by
  unfold Obs.merge
  simp only [Obs.mk.injEq]
  exact ⟨unionBy_assoc tyOrder a.seen b.seen c.seen ha hb hc,
         Nat.add_assoc .., Nat.add_assoc .., Nat.add_assoc .., Bool.or_assoc ..⟩

/-! ## One table's observations -/

theorem TableObs.merge_ok {a b : TableObs} (ha : TableObsOk a) (hb : TableObsOk b) :
    TableObsOk (TableObs.merge a b) :=
  ⟨mergeBy_sorted strOrder _ _ ha.1 hb.1,
   mergeBy_allV (combine := Obs.merge) (P := ObsOk)
     (fun _ _ hx hy => Obs.merge_ok hx hy) _ _ ha.2 hb.2⟩

theorem TableObs.merge_comm {a b : TableObs} (ha : TableObsOk a) (hb : TableObsOk b) :
    TableObs.merge a b = TableObs.merge b a := by
  unfold TableObs.merge
  simp only [TableObs.mk.injEq]
  exact ⟨Nat.add_comm ..,
         mergeBy_commOn (combine := Obs.merge) (P := ObsOk) strOrder
           (fun _ _ hx hy => Obs.merge_comm hx hy) _ _ ha.1 hb.1 ha.2 hb.2,
         Bool.or_comm .., Bool.or_comm ..⟩

theorem TableObs.merge_assoc {a b c : TableObs}
    (ha : TableObsOk a) (hb : TableObsOk b) (hc : TableObsOk c) :
    TableObs.merge (TableObs.merge a b) c = TableObs.merge a (TableObs.merge b c) := by
  unfold TableObs.merge
  simp only [TableObs.mk.injEq]
  exact ⟨Nat.add_assoc ..,
         mergeBy_assocOn (combine := Obs.merge) (P := ObsOk) strOrder
           (fun _ _ hx hy => Obs.merge_ok hx hy)
           (fun _ _ _ hx hy hz => Obs.merge_assoc hx hy hz)
           _ _ _ ha.1 hb.1 hc.1 ha.2 hb.2 hc.2,
         Bool.or_assoc .., Bool.or_assoc ..⟩

/-! ## Every table -/

theorem Tables.merge_ok {a b : Tables} (ha : TablesOk a) (hb : TablesOk b) :
    TablesOk (Tables.merge a b) :=
  ⟨mergeBy_sorted pathOrder _ _ ha.1 hb.1,
   mergeBy_allV (combine := TableObs.merge) (P := TableObsOk)
     (fun _ _ hx hy => TableObs.merge_ok hx hy) _ _ ha.2 hb.2⟩

theorem Tables.merge_comm {a b : Tables} (ha : TablesOk a) (hb : TablesOk b) :
    Tables.merge a b = Tables.merge b a :=
  mergeBy_commOn (combine := TableObs.merge) (P := TableObsOk) pathOrder
    (fun _ _ hx hy => TableObs.merge_comm hx hy) _ _ ha.1 hb.1 ha.2 hb.2

theorem Tables.merge_assoc {a b c : Tables}
    (ha : TablesOk a) (hb : TablesOk b) (hc : TablesOk c) :
    Tables.merge (Tables.merge a b) c = Tables.merge a (Tables.merge b c) :=
  mergeBy_assocOn (combine := TableObs.merge) (P := TableObsOk) pathOrder
    (fun _ _ hx hy => TableObs.merge_ok hx hy)
    (fun _ _ _ hx hy hz => TableObs.merge_assoc hx hy hz)
    _ _ _ ha.1 hb.1 hc.1 ha.2 hb.2 hc.2

/-- The form the corpus fold needs: merging two documents into an accumulator
    gives the same answer in either order. -/
theorem Tables.merge_right_comm {b x y : Tables}
    (hb : TablesOk b) (hx : TablesOk x) (hy : TablesOk y) :
    Tables.merge (Tables.merge b x) y = Tables.merge (Tables.merge b y) x := by
  rw [Tables.merge_assoc hb hx hy, Tables.merge_assoc hb hy hx,
      Tables.merge_comm hx hy]

theorem TablesOk.nil : TablesOk [] := ⟨trivial, trivial⟩

/-! ## The singleton collapse keeps the order

`collapse` is the one step in `inferFinish` that changes a table's *path*, so
it is the one step whose effect on the ordering has to be argued rather than
read off a key-preserving `map`. It rebuilds the list by merging one relocated
table at a time into an accumulator, so the merge carries the invariant and
there is nothing new to prove about sortedness itself. -/

theorem collapseObs_ok (S : List Path) (o : Obs) : ObsOk (collapseObs S o) := by
  show SortedK Ty.lt _
  unfold collapseObs
  generalize (o.seen.map (collapseTy S)) = l
  suffices h : ∀ (acc : List Ty), SortedK Ty.lt acc →
      SortedK Ty.lt (l.foldl (fun acc t => unionBy Ty.lt (· == ·) acc [t]) acc) by
    exact h [] trivial
  induction l with
  | nil => intro acc h; exact h
  | cons x xs ih =>
      intro acc h
      exact ih _ (unionBy_sorted tyOrder acc [x] h ⟨trivial, trivial⟩)

theorem collapseTable_ok {S : List Path} {t : TableObs} (h : TableObsOk t) :
    TableObsOk (collapseTable S t) :=
  ⟨sortedBy_map (fun q => by obtain ⟨k, o⟩ := q; rfl) t.members h.1,
   allV_map (fun q _ => by obtain ⟨k, o⟩ := q; exact collapseObs_ok S o) t.members h.2⟩

theorem collapseOnce_ok {S : List Path} {ts : Tables} (h : TablesOk ts) :
    TablesOk (collapseOnce S ts) := by
  unfold collapseOnce
  -- every relocated table is in order, and the accumulator starts that way
  have hall : ∀ pt ∈ ts.map (fun (p, t) => (collapsePath S [] p, collapseTable S t)),
      TablesOk [pt] := by
    intro pt hpt
    obtain ⟨⟨p, t⟩, hmem, rfl⟩ := List.mem_map.mp hpt
    exact ⟨⟨trivial, trivial⟩, ⟨collapseTable_ok (allV_mem h.2 hmem), trivial⟩⟩
  generalize (ts.map (fun (p, t) => (collapsePath S [] p, collapseTable S t))) = l at hall
  suffices hgo : ∀ (l : Tables) (acc : Tables), (∀ pt ∈ l, TablesOk [pt]) → TablesOk acc →
      TablesOk (l.foldl (fun acc pt => Tables.merge acc [pt]) acc) by
    exact hgo l [] hall TablesOk.nil
  intro l
  induction l with
  | nil => intro acc _ hacc; exact hacc
  | cons x xs ih =>
      intro acc hx hacc
      exact ih _ (fun pt hpt => hx pt (List.mem_cons_of_mem _ hpt))
        (Tables.merge_ok hacc (hx x (List.mem_cons_self ..)))

theorem collapseGo_ok : ∀ (n : Nat) {ts : Tables}, TablesOk ts → TablesOk (collapseGo n ts)
  | 0, _, h => h
  | n + 1, ts, h => by
      show TablesOk (if (collapsePoints ts).isEmpty then ts
                     else collapseGo n (collapseOnce (collapsePoints ts) ts))
      by_cases hs : (collapsePoints ts).isEmpty = true
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact collapseGo_ok n (collapseOnce_ok h)

theorem collapse_ok {ts : Tables} (h : TablesOk ts) : TablesOk (collapse ts) :=
  collapseGo_ok ts.length h

theorem TableObsOk.empty : TableObsOk ({} : TableObs) := ⟨trivial, trivial⟩

/-! ## What the walk does to its observations

    The walk only ever touches `Tables` through `upsert`, so the order
    invariant holds of everything it builds. -/

theorem Tables.upsert_ok {ts : Tables} {p : Path} {f : TableObs → TableObs}
    (h : TablesOk ts) (hf : ∀ t, TableObsOk t → TableObsOk (f t)) :
    TablesOk (ts.upsert p f) := by
  unfold Tables.upsert
  split
  · refine ⟨sortedBy_map ?_ ts h.1, allV_map ?_ ts h.2⟩
    · intro pr; obtain ⟨q, t⟩ := pr; by_cases hq : (q == p) = true <;> simp [hq]
    · intro pr hpr; obtain ⟨q, t⟩ := pr
      by_cases hq : (q == p) = true
      · simp only [hq, if_pos]; exact hf t hpr
      · simp only [hq, Bool.false_eq_true]; exact hpr
  · exact ⟨insertBy_sorted pathOrder ts h.1,
           insertBy_allV (P := TableObsOk) (fun _ _ _ hy => hy)
             (hf _ TableObsOk.empty) ts h.2⟩

theorem recordMember_ok {ts : Tables} {p : Path} {k : String} {sn : Seen}
    (h : TablesOk ts) : TablesOk (recordMember ts p k sn) := by
  unfold recordMember
  refine Tables.upsert_ok h ?_
  intro t ht
  have hone : ObsOk (match sn with
      | .null => ({ nulls := 1 } : Obs)
      | .value ty big => { seen := [ty], values := 1, big := big }) := by
    cases sn with
    | null => trivial
    | value ty big => exact ⟨trivial, trivial⟩
  exact ⟨insertBy_sorted strOrder _ ht.1,
         insertBy_allV (P := ObsOk) (fun _ _ hx hy => Obs.merge_ok hx hy) hone _ ht.2⟩

/-! ## What `toSchema` inherits

    `toSchema` no longer sorts: the merges keep everything in order, so it
    reads the lists off as they are. Both `Faithful` fields about distinctness
    come straight from that. -/

theorem toSchema_mem {ts : Tables} {t : Table} (h : t ∈ toSchema ts) :
    ∃ p tob, (p, tob) ∈ ts ∧ t.path = p ∧
      t.columns = tob.members.map fun (k, o) => { name := k, field := o.field } := by
  unfold toSchema at h
  obtain ⟨pt, hpt, heq⟩ := List.mem_map.mp h
  exact ⟨pt.1, pt.2, (sortBy_perm _ ts).mem_iff.mp hpt,
         by rw [← heq], by rw [← heq]⟩

theorem toSchema_paths_nodup {ts : Tables} (h : TablesOk ts) :
    ((toSchema ts).map Table.path).Nodup := by
  have hbase : (ts.map Prod.fst).Nodup := sortedBy_nodup pathOrder ts h.1
  unfold toSchema
  rw [List.map_map]
  exact ((List.Perm.map _ (sortBy_perm _ ts)).symm).nodup hbase

theorem toSchema_members_nodup {ts : Tables} (h : TablesOk ts) :
    ∀ t, t ∈ toSchema ts → (t.columns.map Column.name).Nodup := by
  intro t ht
  obtain ⟨p, tob, hmem, _, hcols⟩ := toSchema_mem ht
  have htob : TableObsOk tob := allV_mem (p := (p, tob)) h.2 hmem
  rw [hcols, List.map_map]
  exact sortedBy_nodup strOrder tob.members htob.1

end Tatami
