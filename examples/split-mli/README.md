# One `.mli` per module: the two ways to do it

Everything here is hand-written, to compare two proposals before either is
implemented. Nothing in `Tatami/` has changed. `./check.sh` compiles every
variant with `ocamlc` and prints what OCaml accepts.

## The problem

Today all modules go into one file, so `module rec` lets them refer to each
other freely. With a collection the references genuinely form a cycle:

```ocaml
module rec Xs : sig
  type t = { id : id; parent_id : Root.id; idx : int; n : int }   (* Xs -> Root *)
end
and Root : sig
  val xs : t -> Xs.t list                                         (* Root -> Xs *)
end
```

`Xs` names `Root.id` — the foreign key. `Root` names `Xs.t` — the join. That
cycle *is* the referential integrity. OCaml compilation units cannot be
mutually recursive, so splitting the file requires removing one of the two
arrows. Cutting the file apart unchanged fails in **both** possible orders:

```
FAIL  b.mli xs.mli root.mli    Error: Unbound module Root   (in xs.mli)
FAIL  b.mli root.mli xs.mli    Error: Unbound module Xs     (in root.mli)
```

## The two documents

`d1-design-note/` is the design note's own document, §2.1 Step 1:

```json
{ "a": 1, "b": { "c": 1, "d": 2 } }
```

It has a nested object but no collection, so no cycle — and therefore **all
three variants compile**. The note's example does not discriminate between the
proposals; it is here because it is the reference everything else is measured
against.

`d2-with-collection/` is the same document with one repeated substructure
added, which is where the two proposals diverge:

```json
{ "a": 1, "b": { "c": 1, "d": 2 }, "xs": [ { "n": 1 }, { "n": 2 } ] }
```

## Option A — a shared `ids.mli`

Removes the `Xs -> Root` arrow. Every table's key type moves into one
generated module, so a foreign key can be named without depending on the
module it points into.

```ocaml
(* ids.mli *)          (* xs.mli *)
type xs                type id = Ids.xs
type b                 type t = { id : id; parent_id : Ids.root; idx : int; n : int }
type root              val get : id -> t

(* root.mli *)
type id = Ids.root
type t = { id : id; a : int; b : B.id }
val get : id -> t
val b : t -> B.t                  (* follows the foreign key into table b *)
val xs : t -> Xs.t list           (* the rows of the collection at .xs *)
```

Compile order `ids, xs, b, root` — deepest-first, **the order tables are
already emitted in**. Accessors stay on the parent, as in the note's §2.1
correspondence ("joining on it → an accessor function"). `Root.id` stays
usable because it is a transparent alias for the abstract `Ids.root`.

- one extra generated file, and `Ids` becomes a reserved module name
- a foreign key into a nested object still reads `B.id`, exactly as the note
  writes it; only a collection back-reference needs `Ids.root`

## Option B — the collection accessor moves to the child

Removes the `Root -> Xs` arrow instead. No shared file; every `id` stays
abstract in its own module, as now.

```ocaml
(* root.mli *)                    (* xs.mli *)
type id                           type id
type t = { id : id; a : int;      type t = { id : id; parent_id : Root.id;
           b : B.id }                        idx : int; n : int }
val get : id -> t                 val get : id -> t
val b : t -> B.t                  val of_root : Root.id -> t list
```

Compile order `b, root, xs`. Note this is **not** deepest-first: a nested
object orders parent-after-child, a collection orders parent-before-child, so
emission needs a real topological sort rather than the current length sort.

- `Root.xs r` becomes `Xs.of_root r.Root.id` — the join reads from the child
- arguably closer to the query it lowers to (`select * from xs where
  parent_id = ?`), which may matter for the Phase 2 work
- departs from the note's §2.1 correspondence, which puts the accessor on the
  table holding the foreign key's target

## What `./check.sh` establishes

| | D1 (no collection) | D2 (with collection) |
|---|---|---|
| naive split | compiles | **fails, both orders** |
| option A | compiles | compiles |
| option B | compiles | compiles |

And for D2, both options keep the foreign key meaningful — checked by
type-checking two consumers against the `.cmi` files:

- `use.ml` — the join in both directions (`Root.t -> Xs.t list`, and
  `Xs.t -> Root.t` through `parent_id`) — **accepted** under both options
- `forge.ml` — fabricating a key from an `int` — **rejected** under both

So referential integrity is not the deciding factor. The decision is where the
join accessor lives, and whether one extra generated module is acceptable.

## The write-up

`splitting-generated-mli.pdf` is this comparison as a 4-page A4 document, for
circulating. `splitting-generated-mli.html` is what it was rendered from:

```sh
google-chrome --headless=new --no-pdf-header-footer --virtual-time-budget=20000 \
  --print-to-pdf=splitting-generated-mli.pdf splitting-generated-mli.html
```

The same page is published at
claude.ai/code/artifact/0380906b-a557-4fab-a501-444c2d58a4ce

## Decided

**Option A.** It is implemented; `Tatami/Gen.lean` emits `ids.mli`/`ids.ml`
and one pair per module. The files here are the hand-written comparison the
decision was made from and are deliberately left as they were --- they show
only the signatures, from before Phase 1 also emitted implementations. For
what the generator actually produces now, run it, or see
`examples/design-note/`.
