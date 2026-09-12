(* An implementation of generated.mli, written by hand.

   This is the half Phase 1 does not produce yet. The generator emits the
   signature; the rows below are what shredding

       { "a": 1, "b": { "c": 1, "d": 2 } }

   would put in the two tables:

       Table root                 Table b
         id  a  b_id                id  c  d
         1   1  1                   1   1  2

   Note the `id` columns are invented here, not taken from the document:
   shredding has to make up keys because the parent and the child now live in
   separate tables and need something to join on. *)

module B = struct
  (* abstract in the signature, an int here *)
  type id = int
  type t = { id : id; c : int; d : int }

  let rows : t list = [ { id = 1; c = 1; d = 2 } ]

  let get (i : id) : t =
    match List.find_opt (fun r -> r.id = i) rows with
    | Some r -> r
    | None -> invalid_arg "B.get: no such row"
end

module Root = struct
  type id = int
  type t = { id : id; a : int; b : B.id }

  (* b = 1 is the foreign key: it names row 1 of table b *)
  let rows : t list = [ { id = 1; a = 1; b = 1 } ]

  let get (i : id) : t =
    match List.find_opt (fun r -> r.id = i) rows with
    | Some r -> r
    | None -> invalid_arg "Root.get: no such row"

  let all () : t list = rows
  let find (k : int) : t option = List.find_opt (fun r -> r.id = k) rows

  (* the accessor: follows the key into table b. This is the join. *)
  let b (r : t) : B.t = B.get r.b
end
