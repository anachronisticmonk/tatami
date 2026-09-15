(* An OCaml value as a bound parameter. *)

let int = Pgx.Value.of_int
let float = Pgx.Value.of_float
let string = Pgx.Value.of_string
let uuid = Pgx.Value.of_string
let bool = Pgx.Value.of_bool
let unit (_ : unit) = Pgx.Value.null

let int_opt = Pgx.Value.opt Pgx.Value.of_int
let float_opt = Pgx.Value.opt Pgx.Value.of_float
let string_opt = Pgx.Value.opt Pgx.Value.of_string
let uuid_opt = Pgx.Value.opt Pgx.Value.of_string
let bool_opt = Pgx.Value.opt Pgx.Value.of_bool
let unit_opt (_ : unit option) = Pgx.Value.null
