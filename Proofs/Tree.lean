import Tatami.Gen
import Tatami.Infer
import Proofs.Wellformed
import Proofs.Sorted

/-!
# The document's tree survives into the signatures

A JSON document nests: objects inside objects, arrays of objects inside
those. Inference turns each nesting into a table, so the corpus induces a
tree -- the root document at the top, and an edge wherever one table's rows
live inside another's.

The claim here is that a reader of the generated `.mli` files recovers that
same tree, by following declarations from the root module. Nothing about the
nesting is lost in the lowering, and nothing is invented.

There are two kinds of edge, and they are recorded at opposite ends:

* a **collection** edge, when a table's rows sit in an array or map held by
  another table. The child records it: `Table.parent`, and in the signature
  the pair `val run_repo_id : t -> Repo.id` and `val of_repo : Repo.id -> t
  list`.

* a **reference** edge, when a member was an object and became a table of its
  own. The parent records it: a column of type `Ty.ref`, and in the signature
  an accessor `val addr : t -> Address.id`. The child sits in no collection,
  so it has no back reference and no `of_`.

The distinction matters for reading a signature back: a child of a collection
*also* declares an accessor returning its parent's key, and that accessor is
not a reference edge. `FileRefEdge` below excludes it by the only means a
reader of the file has -- the absence of the matching `of_`.

## What is stated, and in what order

`gen_tree_complete` and `gen_tree_sound` are the two halves of the
correspondence, and `gen_moduleName_injOn` is what upgrades them from "the
edges agree" to "the tree is the same tree": without it two distinct tables
could share a module name and the file's graph would be a quotient of the
schema's. All three should follow by inversion on the checks `gen` already
performs on its own output, in the manner of `Proofs.Wellformed` -- no
induction through inference, and no appeal to `mangle_injective`.

`reaches_root` is the one with real content, and it is a fact about
*inference*, not about `gen`: nothing above says a table's parent is itself a
table in the schema. A table whose parent is absent is acyclic, well formed,
and unreachable -- it would receive a `create table` from `Loader.ddl` and
never a row, because `genRegistry.kidsOf` finds children by matching
`parent`. So `Rooted` is exactly the statement that the loader visits every
table, and its failure mode is silent.
-/

namespace Tatami

/-! ## The tree the corpus induces -/

/-- `q`'s rows sit in a collection held by `p`. -/
def CollEdge (s : Schema) (p q : Path) : Prop :=
  ∃ t, t ∈ s ∧ t.path = q ∧ t.parent = some p

/-- `p` holds a key into `q`, which was a member that became a table.

    Stated of the table's own columns rather than of `layoutOf`, so that it
    speaks about what was observed and not about what was emitted. The two
    agree on success: `layoutOf` drops a column named `id`, and `keyTyOf`
    refuses a schema whose `id` is a `ref`, so no reference edge is dropped
    with it. -/
def RefEdge (s : Schema) (p q : Path) : Prop :=
  ∃ t, t ∈ s ∧ t.path = p ∧ ∃ c, c ∈ t.columns ∧ c.field.ty = .ref q

/-- Every table is reached from the root by following edges. -/
inductive Reaches (s : Schema) : Path → Prop where
  | root : Reaches s []
  | viaColl {p q : Path} : Reaches s p → CollEdge s p q → Reaches s q
  | viaRef  {p q : Path} : Reaches s p → RefEdge  s p q → Reaches s q

def Rooted (s : Schema) : Prop := ∀ t, t ∈ s → Reaches s t.path

/-! ## What inference guarantees and an arbitrary `Schema` does not

    `gen` is total on `Schema`, deliberately: `Proofs.Wellformed` holds of
    every schema, including ones inference would never build. The tree
    correspondence cannot be, and these are exactly the three places it
    cannot. Each is a fact about schemas that came from a corpus. -/
structure Faithful (s : Schema) : Prop where
  /-- One table per path. `Tables` is an association list keyed by path, so
      inference cannot produce two; `orderGo` drops one of them if it does. -/
  paths : (s.map Table.path).Nodup
  /-- One column per member name, which `checkDistinct` enforces. Without it
      `keyTyOf` could inspect a different `id` column than the one at hand. -/
  members : ∀ t, t ∈ s → (t.columns.map Column.name).Nodup
  /-- No table both sits in a collection held by `q` and holds a key into
      `q`. A `ref` target lies *under* the table and a parent lies above it,
      so inference cannot produce this -- and the signature could not express
      it if it did: the module would declare `of_q` *and* an accessor into
      `q`, and a reader of the file has nothing left to tell a back
      reference from a reference. -/
  noParentRef : ∀ t, t ∈ s → ∀ q, t.parent = some q →
      ¬ ∃ c, c ∈ t.columns ∧ c.field.ty = .ref q
  /-- The table a `parent` names is in the schema. Without it a path could
      name a module that is never emitted, and the tree would not be rooted. -/
  parentsPresent : ∀ t, t ∈ s → ∀ pp, t.parent = some pp → ∃ u, u ∈ s ∧ u.path = pp
  /-- And so is the table a `ref` column names. -/
  refsPresent : ∀ t, t ∈ s → ∀ c, c ∈ t.columns → ∀ q, c.field.ty = .ref q →
      ∃ u, u ∈ s ∧ u.path = q

/-! ## The tree a reader of the signatures sees -/

/-- A key type as it is written in a signature: `Repo.id`. -/
def keyTyExpr (m : String) : TyExpr := .qualified m "id"

/-- `val of_parent : Parent.id -> t list`, whatever it is named. -/
def Module.declaresLookup (m : Module) (parent : String) : Prop :=
  ∃ n, Decl.value n (.arrow (keyTyExpr parent) (.list (.named "t"))) ∈ m.decls

/-- `val c : t -> Target.id`, or the nullable form. -/
def Module.declaresKeyInto (m : Module) (target : String) : Prop :=
  ∃ n, Decl.value n (.arrow (.named "t") (keyTyExpr target)) ∈ m.decls
     ∨ Decl.value n (.arrow (.named "t") (.option (keyTyExpr target))) ∈ m.decls

/-- Module `b` declares a lookup taking `a`'s key, so `b`'s rows sit in a
    collection held by `a`. -/
def FileCollEdge (f : File) (a b : String) : Prop :=
  ∃ m, m ∈ f.modules ∧ m.name = b ∧ m.declaresLookup a

/-- Module `a` declares an accessor returning `b`'s key, and `a` is not
    itself `b`'s collection child -- which is what tells a reader that the
    accessor is a reference and not a back reference. -/
def FileRefEdge (f : File) (a b : String) : Prop :=
  (∃ m, m ∈ f.modules ∧ m.name = a ∧ m.declaresKeyInto b) ∧ ¬ FileCollEdge f b a

/-! ## What `orderTables` keeps

    `gen` emits one module per table of `orderTables s`, so every statement
    below that quantifies over `s` needs to know how that list relates to
    `s` itself. Soundness holds outright; completeness needs the paths to be
    distinct, which `toSchema` gives and an arbitrary `Schema` does not. -/

theorem mem_orderGo_sound {t : Table} :
    ∀ (fuel : Nat) (pending acc : List Table),
      t ∈ orderGo fuel pending acc → t ∈ pending ∨ t ∈ acc := by
  intro fuel
  induction fuel with
  | zero =>
      intro pending acc h
      simp only [orderGo, List.mem_append, List.mem_reverse] at h
      exact h.symm
  | succ n ih =>
      intro pending acc h
      cases pending with
      | nil =>
          simp only [orderGo, List.mem_reverse] at h
          exact Or.inr h
      | cons p ps =>
          rw [orderGo] at h
          split at h
          · simp only [List.mem_append, List.mem_reverse] at h
            exact h.symm
          · rcases ih _ _ h with hr | ha
            · exact Or.inl (List.mem_filter.mp hr).1
            · rcases List.mem_append.mp ha with hy | ha'
              · exact Or.inl (List.mem_filter.mp (List.mem_reverse.mp hy)).1
              · exact Or.inr ha'
          · simp

/-- `List.inj_on_of_nodup_map`, which core does not have and Mathlib is not
    here to supply. -/
theorem inj_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b := by
  intro l
  induction l with
  | nil => intro _ a b ha _ _; cases ha
  | cons x xs ih =>
      intro hn a b ha hb hf
      rw [List.map_cons, List.nodup_cons] at hn
      obtain ⟨hx, hxs⟩ := hn
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · rfl
        · exact absurd (by rw [hf]; exact List.mem_map_of_mem hb') hx
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd (by rw [← hf]; exact List.mem_map_of_mem ha') hx
        · exact ih hxs ha' hb' hf

theorem mem_orderTables_sound {t : Table} {s : Schema} (h : t ∈ orderTables s) : t ∈ s := by
  rcases mem_orderGo_sound _ _ _ h with h' | h'
  · exact h'
  · cases h'

/-- The converse, which needs the paths to be distinct: `orderGo` drops a
    pending table when a *ready* one shares its path, so two tables at one
    path would lose one of the two. `toSchema` cannot produce that -- its
    tables come from an association list keyed by path -- but `gen` is total
    on `Schema`, so the hypothesis has to be carried. -/
theorem mem_orderGo_complete {t : Table} :
    ∀ (fuel : Nat) (pending acc : List Table),
      (pending.map Table.path).Nodup →
      (t ∈ pending ∨ t ∈ acc) → t ∈ orderGo fuel pending acc := by
  intro fuel
  induction fuel with
  | zero =>
      intro pending acc _ h
      simp only [orderGo, List.mem_append, List.mem_reverse]
      exact h.symm
  | succ n ih =>
      intro pending acc hn h
      cases pending with
      | nil =>
          simp only [orderGo, List.mem_reverse]
          rcases h with h | h
          · cases h
          · exact h
      | cons p ps =>
          rw [orderGo]
          split
          · simp only [List.mem_append, List.mem_reverse]
            exact h.symm
          · refine ih _ _ ((List.Sublist.map Table.path List.filter_sublist).nodup hn) ?_
            rcases h with hp | ha
            · by_cases hr : ((p :: ps).filter fun u =>
                  (depsOf u).all fun d => ((acc.map (·.path)).contains d)).any
                    (fun r => r.path == t.path)
              · -- some ready table shares t's path, so by distinctness it is t
                obtain ⟨r, hrm, hrp⟩ := List.any_eq_true.mp hr
                have hrt : r = t :=
                  inj_of_nodup_map hn (List.mem_filter.mp hrm).1 hp (eq_of_beq hrp)
                exact Or.inr (List.mem_append.mpr (Or.inl
                  (List.mem_reverse.mpr (hrt ▸ hrm))))
              · refine Or.inl (List.mem_filter.mpr ⟨hp, ?_⟩)
                simp only [Bool.not_eq_true] at hr
                simp only [hr, Bool.not_false]
            · exact Or.inr (List.mem_append.mpr (Or.inr ha))
          · simp

theorem mem_orderTables_complete {t : Table} {s : Schema}
    (hn : (s.map Table.path).Nodup) (h : t ∈ s) : t ∈ orderTables s :=
  mem_orderGo_complete _ _ _ hn (Or.inl h)

/-! ## Taking `genRaw` apart

    `genRaw` is three `mapM`s and an append, so a module of the result came
    from exactly one of them. These say which. -/




theorem genModule_name {nm : Naming} {t : Table} {m : Module}
    (h : genModule nm t = .ok m) : m.name = moduleName nm t.path := by
  unfold genModule at h
  obtain ⟨_, _, h'⟩ := except_bind_ok h
  cases h'; rfl

/-! ## From an observed member to an emitted column -/

theorem layoutOf_member {nm : Naming} {t : Table} {cols : List Col}
    {c : Column} {col : Col}
    (h : layoutOf nm t = .ok cols) (hc : c ∈ t.columns)
    (hmc : memberCol (generatedNames nm t) c = .ok (some col)) : col ∈ cols := by
  unfold layoutOf at h
  obtain ⟨kt, _, h1⟩ := except_bind_ok h
  obtain ⟨ms, hms, h2⟩ := except_bind_ok h1
  cases h2
  obtain ⟨o, ho, hmo⟩ := mapM_ok_pointwise hms c hc
  rw [hmc] at hmo
  cases hmo
  exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨some col, ho, rfl⟩)

/-- A member that is an object and is not the key becomes a column holding
    that object's key. -/
theorem memberCol_ref {gen : List String} {c : Column} {q : Path} {o : Option Col}
    (hok : memberCol gen c = .ok o) (hid : ¬ (c.name == idColumn) = true)
    (hty : c.field.ty = .ref q) :
    o = some { name := mangle c.name, ty := .ref q
             , nullable := c.field.nullable, kind := .member c.name } := by
  unfold memberCol at hok
  rw [if_neg hid] at hok
  by_cases hg : (gen.contains (mangle c.name)) = true
  · rw [if_pos hg] at hok; cases hok
  · rw [if_neg hg, hty] at hok
    exact (Except.ok.inj hok).symm

/-- With distinct member names, `find?` on the key finds the column that is
    there to be found. -/
theorem find?_id_eq : ∀ {l : List Column}, (l.map Column.name).Nodup →
    ∀ {c : Column}, c ∈ l → c.name = "id" →
    l.find? (fun x => x.name == "id") = some c := by
  intro l
  induction l with
  | nil => intro _ c hc _; cases hc
  | cons x xs ih =>
      intro hn c hc hid
      rw [List.find?_cons]
      by_cases hx : (x.name == "id") = true
      · rw [hx]
        have : x = c :=
          inj_of_nodup_map hn (List.mem_cons_self ..) hc (by rw [eq_of_beq hx, hid])
        rw [this]
      · rw [Bool.not_eq_true] at hx
        rw [hx]
        rcases List.mem_cons.mp hc with rfl | hc'
        · rw [hid] at hx; simp at hx
        · rw [List.map_cons, List.nodup_cons] at hn
          exact ih hn.2 hc' hid

/-- A member called `id` that is an object is refused outright: it would be
    the table's key, and an object is not a key. So a `ref` column that
    survives into a layout is never the key column, and never dropped. -/
theorem keyTyOf_id_not_ref {t : Table} {kt : Ty} {c : Column} {q : Path}
    (h : keyTyOf t = .ok kt) (hn : (t.columns.map Column.name).Nodup)
    (hc : c ∈ t.columns) (hid : c.name = "id") (hty : c.field.ty = .ref q) : False := by
  unfold keyTyOf at h
  rw [find?_id_eq hn hc hid] at h
  dsimp only at h
  by_cases hnull : c.field.nullable = true
  · rw [if_pos hnull] at h; cases h
  · rw [if_neg hnull, hty] at h; cases h

/-- A table whose rows sit in a collection declares the lookup that finds
    them from the holder's key. This is the collection edge, in the file. -/
theorem genModule_lookup {nm : Naming} {t : Table} {m : Module} {pp : Path}
    (h : genModule nm t = .ok m) (hp : t.parent = some pp) :
    Decl.value (childLookupName nm pp)
      (.arrow (.qualified (moduleName nm pp) "id") (.list (.named "t"))) ∈ m.decls := by
  unfold genModule at h
  obtain ⟨cols, _, h'⟩ := except_bind_ok h
  cases h'
  simp [hp]

/-- Every column of the layout becomes an accessor. This is the reference
    edge, in the file, once the column is known to be a `ref`. -/
theorem genModule_accessor {nm : Naming} {t : Table} {m : Module} {cols : List Col} {c : Col}
    (h : genModule nm t = .ok m) (hl : layoutOf nm t = .ok cols) (hc : c ∈ cols) :
    Decl.value c.name (.arrow (.named "t") (colTyExpr nm c)) ∈ m.decls := by
  unfold genModule at h
  obtain ⟨cols', hl', h'⟩ := except_bind_ok h
  rw [hl] at hl'
  cases hl'
  cases h'
  simp only [List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨c, hc, rfl⟩)

theorem genLoader_decls {s : Schema} {nm : Naming} {t : Table} {m : Module}
    (h : genLoader s nm t = .ok m) : m.decls = [] := by
  unfold genLoader at h
  obtain ⟨_, _, h'⟩ := except_bind_ok h
  cases h'; rfl

theorem genRegistry_decls {s : Schema} {nm : Naming} {m : Module}
    (h : genRegistry s nm = .ok m) : m.decls = [] := by
  unfold genRegistry at h; cases h; rfl

theorem noClash_modules {mods : List Module} {f : File}
    (h : noClash mods = .ok f) : f.modules = mods := by
  unfold noClash at h; dsimp only at h
  split at h
  · cases h
  · cases h; rfl

/-- `gen` is `genRaw` followed by a check that returns its input unchanged,
    so inverting it gives the raw file back. -/
theorem gen_inv {nm : Naming} {s : Schema} {f : File} (h : gen nm s = .ok f) :
    genRaw nm s = .ok f := by
  unfold gen at h
  split at h
  · cases h
  cases hg : genRaw nm s with
  | error e => rw [hg] at h; dsimp only at h; cases h
  | ok f' =>
      rw [hg] at h; dsimp only at h
      unfold certify at h
      by_cases hb : f'.okB = true
      · rw [if_pos hb] at h; exact h
      · rw [if_neg hb] at h; cases h

/-- Every module of the file came from one of the three `mapM`s. -/
theorem gen_modules {nm : Naming} {s : Schema} {f : File} (h : gen nm s = .ok f) :
    ∃ units loaders registry,
      (orderTables s).mapM (genModule nm) = .ok units ∧
      (orderTables s).mapM (genLoader s nm) = .ok loaders ∧
      genRegistry s nm = .ok registry ∧
      f.modules = units ++ loaders ++ [registry] := by
  have hg := gen_inv h
  unfold genRaw at hg
  obtain ⟨units, hu, h1⟩ := except_bind_ok hg
  obtain ⟨loaders, hl, h2⟩ := except_bind_ok h1
  obtain ⟨registry, hr, h3⟩ := except_bind_ok h2
  refine ⟨units, loaders, registry, hu, hl, hr, ?_⟩
  exact noClash_modules h3

/-! ## `gen` establishes `Faithful` itself

    The conditions above are not assumed of the caller: `gen` checks them and
    refuses a schema that fails, so every file the generator emits satisfies
    them. Proved by inverting that check, in the manner of `gen_wellFormed`. -/

theorem nodupPaths_sound : ∀ {l : List Path}, nodupPaths l = true → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons p ps ih =>
      intro h
      simp only [nodupPaths, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
                 Bool.not_true] at h
      refine List.nodup_cons.mpr ⟨?_, ih h.2⟩
      intro hmem
      have hc : ps.contains p = true := List.contains_iff_mem.mpr hmem
      rw [h.1] at hc
      simp at hc

theorem gen_schemaOk {nm : Naming} {s : Schema} {f : File} (h : gen nm s = .ok f) :
    schemaOkB s = true := by
  by_cases hb : schemaOkB s = true
  · exact hb
  · unfold gen at h
    rw [if_pos (by simp [hb])] at h
    cases h

/-- A path the check found in the schema is a table of it. -/
private theorem path_mem {s : Schema} {p : Path}
    (h : (s.map Table.path).contains p = true) : ∃ u, u ∈ s ∧ u.path = p := by
  obtain ⟨u, hu, hup⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
  exact ⟨u, hu, hup⟩

theorem gen_faithful (nm : Naming) (s : Schema) (f : File) (h : gen nm s = .ok f) :
    Faithful s := by
  have hb := gen_schemaOk h
  simp only [schemaOkB, Bool.and_eq_true, List.all_eq_true] at hb
  obtain ⟨⟨hpaths, hper⟩, _⟩ := hb
  refine
    { paths := nodupPaths_sound hpaths
      members := ?_, noParentRef := ?_, parentsPresent := ?_, refsPresent := ?_ }
  · intro t ht
    exact nodupNames_sound (hper t ht).1.1
  · rintro t ht q hq ⟨c, hc, hcty⟩
    have hpar := (hper t ht).1.2
    rw [hq] at hpar
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
               List.any_eq_false] at hpar
    have hno := hpar.2 c hc
    rw [hcty] at hno
    simp at hno
  · intro t ht pp hq
    have hpar := (hper t ht).1.2
    rw [hq] at hpar
    simp only [Bool.and_eq_true] at hpar
    exact path_mem hpar.1
  · intro t ht c hc q hcty
    have hr := (hper t ht).2 c hc
    rw [hcty] at hr
    exact path_mem hr

/-! ## And rootedness, the same way

    A table the walk from the root never reaches would receive a
    `create table` from `Loader.ddl` and never a row, because
    `genRegistry.kidsOf` finds children by matching `parent`. So the
    generator refuses one. -/

theorem stepReach_sound {s : Schema} {acc : List Path}
    (hacc : ∀ p, p ∈ acc → Reaches s p) : ∀ p, p ∈ stepReach s acc → Reaches s p := by
  intro p hp
  simp only [stepReach] at hp
  rcases List.mem_append.mp hp with h1 | h2
  · rcases List.mem_append.mp h1 with h | h
    · exact hacc p h
    · obtain ⟨t, ht, hsome⟩ := List.mem_filterMap.mp h
      cases hpar : t.parent with
      | none => rw [hpar] at hsome; cases hsome
      | some pp =>
          rw [hpar] at hsome
          dsimp only at hsome
          by_cases hcond : (acc.contains pp && !acc.contains t.path) = true
          · rw [if_pos hcond] at hsome
            cases hsome
            simp only [Bool.and_eq_true] at hcond
            exact Reaches.viaColl (hacc pp (List.contains_iff_mem.mp hcond.1))
              ⟨t, ht, rfl, hpar⟩
          · rw [if_neg hcond] at hsome; cases hsome
  · obtain ⟨t, ht, hmem⟩ := List.mem_flatMap.mp h2
    by_cases hin : (acc.contains t.path) = true
    · rw [if_pos hin] at hmem
      obtain ⟨c, hc, hsome⟩ := List.mem_filterMap.mp hmem
      cases hty : c.field.ty with
      | ref q =>
          rw [hty] at hsome
          dsimp only at hsome
          by_cases hq : (acc.contains q) = true
          · rw [if_pos hq] at hsome; cases hsome
          · rw [if_neg hq] at hsome
            cases hsome
            exact Reaches.viaRef (hacc t.path (List.contains_iff_mem.mp hin))
              ⟨t, ht, rfl, c, hc, hty⟩
      | _ => rw [hty] at hsome; cases hsome
    · rw [if_neg hin] at hmem; cases hmem

theorem reachGo_sound {s : Schema} : ∀ (fuel : Nat) (acc : List Path),
    (∀ p, p ∈ acc → Reaches s p) → ∀ p, p ∈ reachGo s fuel acc → Reaches s p := by
  intro fuel
  induction fuel with
  | zero => intro acc hacc p hp; rw [reachGo] at hp; exact hacc p hp
  | succ n ih =>
      intro acc hacc p hp
      rw [reachGo] at hp
      split at hp
      · exact hacc p hp
      · exact ih _ (stepReach_sound hacc) p hp

theorem reachable_sound {s : Schema} : ∀ p, p ∈ reachable s → Reaches s p := by
  refine reachGo_sound _ _ ?_
  intro p hp
  rcases List.mem_singleton.mp hp with rfl
  exact Reaches.root

/-- Every table is reachable from the root, so walking the generated
    signatures from the root module enumerates the whole schema. -/
theorem gen_rooted (nm : Naming) (s : Schema) (f : File) (h : gen nm s = .ok f) :
    Rooted s := by
  have hb := gen_schemaOk h
  simp only [schemaOkB, Bool.and_eq_true, List.all_eq_true] at hb
  intro t ht
  exact reachable_sound t.path (List.contains_iff_mem.mp (hb.2 t ht))

/-! ## The correspondence -/

theorem genModule_layout {nm : Naming} {t : Table} {m : Module}
    (h : genModule nm t = .ok m) : ∃ cols, layoutOf nm t = .ok cols := by
  unfold genModule at h
  obtain ⟨cols, hc, _⟩ := except_bind_ok h
  exact ⟨cols, hc⟩

theorem layoutOf_keyTy {nm : Naming} {t : Table} {cols : List Col}
    (h : layoutOf nm t = .ok cols) : ∃ kt, keyTyOf t = .ok kt := by
  unfold layoutOf at h
  obtain ⟨kt, hk, _⟩ := except_bind_ok h
  exact ⟨kt, hk⟩

theorem layoutOf_mapM {nm : Naming} {t : Table} {cols : List Col}
    (h : layoutOf nm t = .ok cols) :
    ∃ ms, t.columns.mapM (memberCol (generatedNames nm t)) = .ok ms := by
  unfold layoutOf at h
  obtain ⟨_, _, h1⟩ := except_bind_ok h
  obtain ⟨ms, hms, _⟩ := except_bind_ok h1
  exact ⟨ms, hms⟩

/-- The module of a table of the schema, and the fact that it is in the file. -/
theorem gen_module_of {nm : Naming} {s : Schema} {f : File} {t : Table}
    (h : gen nm s = .ok f) (ht : t ∈ s) :
    ∃ m, m ∈ f.modules ∧ genModule nm t = .ok m := by
  have hf := gen_faithful nm s f h
  obtain ⟨units, loaders, registry, hu, _, _, hmods⟩ := gen_modules h
  obtain ⟨m, hm, hgm⟩ := mapM_ok_pointwise hu t (mem_orderTables_complete hf.paths ht)
  exact ⟨m, by rw [hmods]; exact List.mem_append_left _ (List.mem_append_left _ hm), hgm⟩

/-- A module carrying any declaration at all is some table's, and this says
    which table and that `genModule` produced it. -/
theorem gen_module_source {nm : Naming} {s : Schema} {f : File} {m : Module}
    (h : gen nm s = .ok f) (hm : m ∈ f.modules) (hd : m.decls ≠ []) :
    ∃ t, t ∈ s ∧ genModule nm t = .ok m := by
  obtain ⟨units, loaders, registry, hu, hl, hr, hmods⟩ := gen_modules h
  rw [hmods] at hm
  rcases List.mem_append.mp hm with hm' | hreg
  · rcases List.mem_append.mp hm' with hunit | hload
    · obtain ⟨t, ht, hgm⟩ := mem_of_mapM_ok hu m hunit
      exact ⟨t, mem_orderTables_sound ht, hgm⟩
    · obtain ⟨t, _, hgl⟩ := mem_of_mapM_ok hl m hload
      exact absurd (genLoader_decls hgl) hd
  · rw [List.mem_singleton.mp hreg] at hd
    exact absurd (genRegistry_decls hr) hd

/-- The only declaration of the shape a collection edge has is the lookup,
    and it names the table these rows sit in. So a reader who finds one has
    found a parent, not something else that happens to look like one. -/
theorem genModule_lookup_only {nm : Naming} {t : Table} {m : Module} {a n : String}
    (h : genModule nm t = .ok m)
    (hd : Decl.value n ((TyExpr.qualified a "id").arrow (TyExpr.list (TyExpr.named "t")))
            ∈ m.decls) :
    ∃ pp, t.parent = some pp ∧ a = moduleName nm pp := by
  unfold genModule at h
  obtain ⟨cols, _, h'⟩ := except_bind_ok h
  cases h'
  simp only [List.mem_append, List.mem_map, List.mem_cons] at hd
  cases hp : t.parent with
  | none =>
      exfalso
      rw [hp] at hd
      cases cols <;> simp_all
  | some pp =>
      refine ⟨pp, rfl, ?_⟩
      rw [hp] at hd
      cases cols <;> simp_all

/-- Only a `ref` column is typed as another module's key. `tyExprOf` sends a
    collection to a `list` and every scalar to a scalar, so nothing else can
    produce `M.id`. -/
theorem colTyExpr_ref {nm : Naming} {c : Col} {a : String}
    (h : colTyExpr nm c = TyExpr.qualified a "id" ∨
         colTyExpr nm c = (TyExpr.qualified a "id").option) :
    ∃ p, c.ty = .ref p ∧ a = moduleName nm p := by
  unfold colTyExpr at h
  cases hty : c.ty <;> by_cases hn : c.nullable <;> simp_all [tyExprOf]

/-- The only declarations taking a row and returning something that is not
    itself a function are the accessors, one per column of the layout. `get`
    takes `id` rather than `t`, a setter returns a function, and `make` is
    labelled. -/
theorem genModule_accessor_only {nm : Naming} {t : Table} {m : Module}
    {n : String} {X : TyExpr}
    (h : genModule nm t = .ok m)
    (hd : Decl.value n ((TyExpr.named "t").arrow X) ∈ m.decls)
    (hX : ∀ Y Z, X ≠ TyExpr.arrow Y Z) :
    ∃ cols c, layoutOf nm t = .ok cols ∧ c ∈ cols ∧ X = colTyExpr nm c := by
  unfold genModule at h
  obtain ⟨cols, hcols, h'⟩ := except_bind_ok h
  cases h'
  refine ⟨cols, ?_⟩
  simp only [List.mem_append, List.mem_map, List.mem_cons] at hd
  cases hp : t.parent <;> rw [hp] at hd <;> simp_all <;>
    rcases hd with (⟨_, hmk⟩ | ⟨c, hc, _, hX'⟩) | ⟨c, _, _, hX'⟩
  · cases cols <;> simp at hmk
  · exact ⟨c, hc, hX'.symm⟩
  · exact absurd hX'.symm (hX _ _)
  · cases cols <;> simp at hmk
  · exact ⟨c, hc, hX'.symm⟩
  · exact absurd hX'.symm (hX _ _)

/-- A key is never an object: `keyTyOf` refuses one. -/
theorem keyTyOf_not_ref {t : Table} {kt : Ty} {p : Path}
    (h : keyTyOf t = .ok kt) : kt ≠ .ref p := by
  unfold keyTyOf at h
  cases hfind : t.columns.find? (fun c => c.name == "id") with
  | none => rw [hfind] at h; cases h; simp
  | some c =>
      rw [hfind] at h; dsimp only at h
      by_cases hn : c.field.nullable = true
      · rw [if_pos hn] at h; cases h
      · rw [if_neg hn] at h
        cases hty : c.field.ty <;> rw [hty] at h <;> cases h <;> simp

/-- A column of the layout is either one the table's position put there or
    one a member of the document put there. -/
theorem mem_layoutOf {nm : Naming} {t : Table} {cols : List Col} {c : Col}
    (h : layoutOf nm t = .ok cols) (hc : c ∈ cols) :
    (∃ kt, keyTyOf t = .ok kt ∧ c ∈ baseCols nm t kt) ∨
    (∃ col, col ∈ t.columns ∧ memberCol (generatedNames nm t) col = .ok (some c)) := by
  unfold layoutOf at h
  obtain ⟨kt, hkt, h1⟩ := except_bind_ok h
  obtain ⟨ms, hms, h2⟩ := except_bind_ok h1
  cases h2
  rcases List.mem_append.mp hc with hb | hm
  · exact Or.inl ⟨kt, hkt, hb⟩
  · obtain ⟨o, ho, hid⟩ := List.mem_filterMap.mp hm
    obtain ⟨col, hcol, hmc⟩ := mem_of_mapM_ok hms o ho
    refine Or.inr ⟨col, hcol, ?_⟩
    rw [hmc]
    cases o <;> simp_all

/-- A member column keeps the member's type. -/
theorem memberCol_ty {gen : List String} {c : Column} {col : Col}
    (h : memberCol gen c = .ok (some col)) : col.ty = c.field.ty := by
  unfold memberCol at h
  by_cases hid : (c.name == idColumn) = true
  · rw [if_pos hid] at h; cases h
  · rw [if_neg hid] at h
    by_cases hg : (gen.contains (mangle c.name)) = true
    · rw [if_pos hg] at h; cases h
    · rw [if_neg hg] at h
      cases hty : c.field.ty <;> rw [hty] at h <;> cases h <;> simp

/-- Of the columns a table's position puts there, only the back reference is
    a key into another table -- a key is never an object, and a position is a
    string or an integer. So a base column typed `M.id` *is* the back
    reference, and names the table these rows sit in. -/
theorem baseCols_ref {nm : Naming} {t : Table} {kt : Ty} {c : Col} {p : Path}
    (hkt : keyTyOf t = .ok kt) (hc : c ∈ baseCols nm t kt) (hty : c.ty = .ref p) :
    t.parent = some p := by
  unfold baseCols at hc
  cases hp : t.parent with
  | none =>
      rw [hp] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      exact absurd hty (keyTyOf_not_ref hkt)
  | some pp =>
      rw [hp] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact absurd hty (keyTyOf_not_ref hkt)
      · simp_all
      · by_cases hk : t.keyed <;> simp_all

/-- What upgrades the two halves above from an agreement of edges to an
    isomorphism of trees. `gen` refuses a file whose module names repeat, so
    this is available by inversion on that check rather than from any property
    of `mangle` -- which matters now that `Naming.tables` lets a configuration
    name two paths the same thing. -/
theorem gen_moduleName_injOn (nm : Naming) (s : Schema) (f : File)
    (h : gen nm s = .ok f) :
    ∀ t u, t ∈ s → u ∈ s → moduleName nm t.path = moduleName nm u.path → t.path = u.path := by
  have hf := gen_faithful nm s f h
  obtain ⟨units, loaders, registry, hu, _, _, hmods⟩ := gen_modules h
  -- the generator refuses a file whose module names repeat, and
  -- `Proofs.Wellformed` has already turned that check into the proposition
  have hnd : (f.modules.map Module.name).Nodup := (gen_wellFormed nm s f h).1
  have hpre : (units.map Module.name).Sublist (f.modules.map Module.name) := by
    rw [hmods, List.append_assoc, List.map_append]
    exact List.sublist_append_left _ _
  have hunits : (units.map Module.name).Nodup := hpre.nodup hnd
  -- and a unit's name is its table's module name, so the names of the tables
  -- in compile order are distinct
  rw [mapM_ok_map (fun t m hm => genModule_name hm) hu] at hunits
  intro t u ht hu' hname
  have := inj_of_nodup_map hunits
    (mem_orderTables_complete hf.paths ht) (mem_orderTables_complete hf.paths hu') hname
  rw [this]

/-- Nothing in the tree is lost: every edge the corpus induces is declared. -/
theorem gen_tree_complete_coll (nm : Naming) (s : Schema) (f : File)
    (h : gen nm s = .ok f) :
    ∀ p q, CollEdge s p q → FileCollEdge f (moduleName nm p) (moduleName nm q) := by
  have hf := gen_faithful nm s f h
  rintro p q ⟨t, ht, htp, htpar⟩
  obtain ⟨m, hm, hgm⟩ := gen_module_of h ht
  exact ⟨m, hm, by rw [genModule_name hgm, htp],
         ⟨childLookupName nm p, genModule_lookup hgm htpar⟩⟩

theorem gen_tree_complete_ref (nm : Naming) (s : Schema) (f : File)
    (h : gen nm s = .ok f) :
    ∀ p q, RefEdge s p q → FileRefEdge f (moduleName nm p) (moduleName nm q) := by
  have hf := gen_faithful nm s f h
  rintro p q ⟨t, ht, htp, c, hc, hcty⟩
  obtain ⟨m, hm, hgm⟩ := gen_module_of h ht
  obtain ⟨cols, hcols⟩ := genModule_layout hgm
  obtain ⟨kt, hkt⟩ := layoutOf_keyTy hcols
  obtain ⟨ms, hms⟩ := layoutOf_mapM hcols
  -- the member is not the key: a key that is an object is refused outright
  have hidne : ¬ (c.name == idColumn) = true := fun hEq =>
    keyTyOf_id_not_ref hkt (hf.members t ht) hc (eq_of_beq hEq) hcty
  obtain ⟨o, ho, hmo⟩ := mapM_ok_pointwise hms c hc
  have hos := memberCol_ref hmo hidne hcty
  rw [hos] at hmo
  have hcolmem := layoutOf_member hcols hc hmo
  have hacc := genModule_accessor hgm hcols hcolmem
  refine ⟨⟨m, hm, by rw [genModule_name hgm, htp], ?_⟩, ?_⟩
  · -- the accessor returns `q`'s key, one `option` deep where the member is
    refine ⟨mangle c.name, ?_⟩
    by_cases hnull : c.field.nullable = true
    · exact Or.inr (by simpa [colTyExpr, keyTyExpr, hnull] using hacc)
    · exact Or.inl (by simpa [colTyExpr, keyTyExpr, hnull] using hacc)
  · -- and this is a reference, not a back reference: were it a back
    -- reference, `t` would sit in a collection held by `q` *and* hold a key
    -- into `q`, which `Faithful.noParentRef` excludes
    rintro ⟨m', hm', hm'name, lk, hlk⟩
    obtain ⟨t', ht', hgm'⟩ := gen_module_source h hm' (by intro e; rw [e] at hlk; cases hlk)
    obtain ⟨pp, hpar, hqpp⟩ := genModule_lookup_only hgm' hlk
    have hpath : t'.path = t.path := by
      refine gen_moduleName_injOn nm s f h t' t ht' ht ?_
      rw [← genModule_name hgm', hm'name, htp]
    have htt' : t' = t := inj_of_nodup_map hf.paths ht' ht hpath
    rw [htt'] at hpar
    obtain ⟨u, hu, hup⟩ := hf.parentsPresent t ht pp hpar
    obtain ⟨v, hv, hvp⟩ := hf.refsPresent t ht c hc q hcty
    have : q = pp := by
      have := gen_moduleName_injOn nm s f h v u hv hu (by rw [hvp, hup]; exact hqpp)
      rw [hvp, hup] at this; exact this
    rw [this] at hcty
    exact hf.noParentRef t ht pp hpar ⟨c, hc, hcty⟩

theorem gen_tree_complete (nm : Naming) (s : Schema) (f : File)
    (h : gen nm s = .ok f) :
    (∀ p q, CollEdge s p q → FileCollEdge f (moduleName nm p) (moduleName nm q)) ∧
    (∀ p q, RefEdge  s p q → FileRefEdge  f (moduleName nm p) (moduleName nm q)) :=
  ⟨gen_tree_complete_coll nm s f h, gen_tree_complete_ref nm s f h⟩

/-- Nothing is invented: every edge a reader finds between two tables of the
    schema is an edge the corpus induced. -/
theorem gen_tree_sound (nm : Naming) (s : Schema) (f : File)
    (h : gen nm s = .ok f) :
    (∀ t u, t ∈ s → u ∈ s →
        FileCollEdge f (moduleName nm t.path) (moduleName nm u.path) →
        CollEdge s t.path u.path) ∧
    (∀ t u, t ∈ s → u ∈ s →
        FileRefEdge f (moduleName nm t.path) (moduleName nm u.path) →
        RefEdge s t.path u.path) := by
  have hf := gen_faithful nm s f h
  constructor
  · rintro t u ht hu ⟨m', hm', hm'name, lk, hlk⟩
    obtain ⟨w, hw, hgw⟩ := gen_module_source h hm' (by intro e; rw [e] at hlk; cases hlk)
    obtain ⟨pp, hpar, hmn⟩ := genModule_lookup_only hgw hlk
    have hwu : w = u :=
      inj_of_nodup_map hf.paths hw hu
        (gen_moduleName_injOn nm s f h w u hw hu (by rw [← genModule_name hgw, hm'name]))
    rw [hwu] at hpar
    obtain ⟨v, hv, hvp⟩ := hf.parentsPresent u hu pp hpar
    have hteq : t.path = pp := by
      have := gen_moduleName_injOn nm s f h t v ht hv (by rw [hvp]; exact hmn)
      rw [hvp] at this; exact this
    exact ⟨u, hu, rfl, by rw [hteq]; exact hpar⟩
  · rintro t u ht hu ⟨⟨m', hm', hm'name, n, hkey⟩, hnot⟩
    have hne : m'.decls ≠ [] := by
      rcases hkey with hk | hk <;> intro e <;> rw [e] at hk <;> cases hk
    obtain ⟨w, hw, hgw⟩ := gen_module_source h hm' hne
    have hwt : w = t :=
      inj_of_nodup_map hf.paths hw ht
        (gen_moduleName_injOn nm s f h w t hw ht (by rw [← genModule_name hgw, hm'name]))
    rw [hwt] at hgw
    obtain ⟨cols, c, hcols, hc, hX⟩ :
        ∃ cols c, layoutOf nm t = .ok cols ∧ c ∈ cols ∧
          (colTyExpr nm c = TyExpr.qualified (moduleName nm u.path) "id" ∨
           colTyExpr nm c = (TyExpr.qualified (moduleName nm u.path) "id").option) := by
      rcases hkey with hk | hk
      · obtain ⟨cs, c, h1, h2, h3⟩ :=
          genModule_accessor_only hgw hk (by intro Y Z; simp [keyTyExpr])
        exact ⟨cs, c, h1, h2, Or.inl h3.symm⟩
      · obtain ⟨cs, c, h1, h2, h3⟩ :=
          genModule_accessor_only hgw hk (by intro Y Z; simp [keyTyExpr])
        exact ⟨cs, c, h1, h2, Or.inr h3.symm⟩
    obtain ⟨p, hcp, hmn⟩ := colTyExpr_ref hX
    rcases mem_layoutOf hcols hc with ⟨kt, hkt, hbase⟩ | ⟨col, hcol, hmc⟩
    · -- a base column typed as a key is the back reference, and then the
      -- module declares the lookup that `hnot` says it does not
      exact absurd ⟨m', hm', hm'name, childLookupName nm p,
        by rw [hmn]; exact genModule_lookup hgw (baseCols_ref hkt hbase hcp)⟩ hnot
    · have hcolty : col.field.ty = .ref p := by rw [← memberCol_ty hmc]; exact hcp
      obtain ⟨v, hv, hvp⟩ := hf.refsPresent t ht col hcol p hcolty
      have hup : u.path = p := by
        have := gen_moduleName_injOn nm s f h u v hu hv (by rw [hvp]; exact hmn)
        rw [hvp] at this; exact this
      exact ⟨t, ht, rfl, col, hcol, by rw [hup]; exact hcolty⟩

/-- And no other module carries an edge, so the two graphs have the same
    vertices as well as the same edges. The loaders and the registry are
    emitted `implOnly`, with no `decls` at all. -/
theorem gen_edges_only_on_tables (nm : Naming) (s : Schema) (f : File)
    (h : gen nm s = .ok f) :
    ∀ m, m ∈ f.modules → m.decls ≠ [] → ∃ t, t ∈ s ∧ m.name = moduleName nm t.path := by
  obtain ⟨units, loaders, registry, hu, hl, hr, hmods⟩ := gen_modules h
  intro m hm hd
  rw [hmods] at hm
  rcases List.mem_append.mp hm with hm' | hreg
  · rcases List.mem_append.mp hm' with hunit | hload
    · -- a table's own module: its name is the table's module name
      obtain ⟨t, ht, hgm⟩ := mem_of_mapM_ok hu m hunit
      exact ⟨t, mem_orderTables_sound ht, genModule_name hgm⟩
    · -- a loader has no signature at all, so it carries no edge
      obtain ⟨t, _, hgl⟩ := mem_of_mapM_ok hl m hload
      exact absurd (genLoader_decls hgl) hd
  · -- and neither does the registry
    rw [List.mem_singleton.mp hreg] at hd
    exact absurd (genRegistry_decls hr) hd

/-! ## The tree is a tree -/

/-- Following a parent drops the collection marker and the member holding it,
    so it strictly shortens the path. Hence no cycles, and the walk up from
    any table terminates. -/
theorem parentOfElement_shorter {p q : Path} (h : Path.parentOfElement p = some q) :
    q.length + 2 = p.length := by
  have hlen : p.reverse.length = p.length := List.length_reverse
  unfold Path.parentOfElement at h
  split at h <;> rename_i heq <;> simp_all [List.length_reverse]

/-! ## A note on where the guarantee comes from

    `Faithful` and `Rooted` are established by `gen` checking its input, not
    by a theorem about inference. That is the stronger arrangement for a
    reader of the output -- the properties hold of *every* file the generator
    emits, whatever it was given -- and the weaker one for a reader of the
    corpus, since it does not by itself say inference never trips the check.
    Nothing inference produces does: `Tables` is keyed by path,
    `checkDistinct` refuses a repeated member, and the walk records a table
    before descending into what it holds, so a parent and a reference target
    are always present and a reference always points one segment down while a
    parent points two up. Turning that paragraph into a theorem is the
    remaining work, and `Proofs.Walk` has the induction it would use. -/

end Tatami
