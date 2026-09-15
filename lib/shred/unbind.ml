(* A bound parameter back as an OCaml value.

   The engine carries a row's key, its parent's key and its position as bound
   values, because it does not know what any given table stores those as. The
   loader does know -- the layout told it -- so the conversion back happens
   there, one call per column, with the type the layout named. *)

let int v = Pgx.Value.to_int_exn v
let float v = Pgx.Value.to_float_exn v
let string v = Pgx.Value.to_string_exn v
let uuid v = Pgx.Value.to_string_exn v
let bool v = Pgx.Value.to_bool_exn v
let unit _ = ()
