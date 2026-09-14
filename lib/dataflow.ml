(* Constant propagation, and why the signature makes it sharper.

   The textbook framework: a lattice of facts, a transfer function per
   statement built from GEN and KILL, and a meet at every point where control
   flow joins, iterated to a fixpoint. Height is what guarantees termination,
   so the lattice comes first and everything else is arranged around it.

   Worth saying plainly, because it is the usual first confusion: constant
   propagation is *not* a bit-vector problem. Reaching definitions and
   available expressions are -- there GEN and KILL are fixed sets, computable
   from the statement alone, and the framework is distributive. Here GEN
   depends on IN: whether [t1 = a * b] generates a constant depends on what a
   and b are known to be on the way in. That is why it is presented as a
   monotone framework over a lattice rather than as two bitmasks, and why the
   Dragon Book uses it as its example of a framework that is not distributive.

   What Tatami changes is not the algorithm -- it is where the algorithm
   starts. Classical constant propagation over a program that reads its input
   must initialise every input to Top, because nothing is known about what
   arrives. Our leaves are generated accessors, and the .mli says exactly what
   each one is:

     val qty   : t -> int            a dense int, and never absent
     val note  : t -> string option  text, and absent on some rows

   So the analysis begins with facts rather than with Top. A conservative
   analysis becomes an exact one, not by being cleverer, but because we emitted
   the leaves and therefore know them. That is the whole claim of the project,
   restated for a dataflow pass. *)

(* ---- the constant lattice ------------------------------------------------ *)

(*      Top          not a constant (NAC): two paths disagreed, or the value
       / | \         came from something we cannot evaluate
     c1 c2 c3 ...    exactly this value
       \ | /
        Bot          nothing known yet -- the starting point, and on an
                     unreachable path the value it keeps

   Height three, so the iteration cannot descend forever: a fact can move
   Bot -> Const -> Top and never back. *)
type const = Bot | Const of Query.value | Top

(* ---- the nullability lattice --------------------------------------------- *)

(* Two points, and the order that matters is which one is the conservative
   answer. [Maybe] is the top: if two paths disagree about whether a value can
   be absent, the safe answer is that it can. [Never] is a promise, and only
   the signature or a literal can make it. *)
type nullity = Never | Maybe

(* ---- what is known about one value -------------------------------------- *)

(* The two run alongside each other rather than being folded into one lattice,
   because they answer different questions and the second is the one with
   teeth. [value] decides whether an expression can be replaced by a constant.
   [nullity] decides whether the column holding its result needs a validity
   array at all -- which is a decision about memory, not about arithmetic. *)
type fact = { value : const; nullity : nullity }

let unknown = { value = Bot; nullity = Maybe }
let nac = { value = Top; nullity = Maybe }

(* A literal in the query text is the easy case: it is exactly itself, and a
   literal is never NULL. *)
let literal v = { value = Const v; nullity = Never }

(* And this is the case the project exists to make. Nothing is known about the
   value -- a column is not a constant -- but the layout is known exactly, so
   the second component is a fact rather than a concession. *)
let column (c : Schema.column) =
  { value = Top;
    nullity = (match c.layout with Schema.Nullable _ -> Maybe | Schema.Plain _ -> Never) }

(* ---- meet ---------------------------------------------------------------- *)

(* The join point operator. Two paths reach here; what is true on both?

   Note [Const a] meet [Const b] with a <> b collapsing to [Top] rather than
   to a set. Keeping the set would be a more precise analysis and a different
   lattice -- of unbounded height, so termination would stop being free. *)
let meet_const a b =
  match (a, b) with
  | Bot, x | x, Bot -> x
  | Top, _ | _, Top -> Top
  | Const x, Const y -> if x = y then Const x else Top

(* [Never] only survives if both paths promise it. *)
let meet_nullity a b = match (a, b) with Never, Never -> Never | _ -> Maybe

let meet a b =
  { value = meet_const a.value b.value; nullity = meet_nullity a.nullity b.nullity }

(* Whether the iteration has stopped. Structural equality is enough: both
   components are finite and small, and [Query.value] is a flat variant. *)
let equal a b = a.value = b.value && a.nullity = b.nullity

(* ---- rendering ----------------------------------------------------------- *)

(* Printed the way the analysis is taught, so a reader can check the fixpoint
   by hand against the tables on the page. *)
let const_to_string = function
  | Bot -> "_|_"
  | Top -> "NAC"
  | Const v -> Query.value_to_string v

let nullity_to_string = function Never -> "not null" | Maybe -> "may be null"

let to_string f =
  Printf.sprintf "%s, %s" (const_to_string f.value) (nullity_to_string f.nullity)
