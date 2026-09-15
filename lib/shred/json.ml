(* Reading a document member by the JSON name it actually has.

   The generator emits the unmangled name here and the mangled one everywhere
   else, so this is the only place the two spellings meet: [Json.bool doc
   "private"] filling a column called [private_]. *)

open Yojson.Safe.Util

(* An absent member and an explicit null are the same thing: JSON expresses
   optionality both ways, and the schema says only that the column is
   optional. A non-object has no members at all, which is the same answer
   again rather than an error -- a reference to an object that is not there
   reads as absent. *)
let mem d k =
  match d with
  | `Assoc _ -> (match member k d with `Null -> None | v -> Some v)
  | _ -> None

let req d k =
  match mem d k with
  | Some v -> v
  | None ->
    failwith (Printf.sprintf "%s: missing, though the schema does not say it is optional" k)

let int d k = to_int (req d k)
let string d k = to_string (req d k)
let uuid d k = to_string (req d k)
let bool d k = to_bool (req d k)
let unit _ _ = ()

(* an int where a float is expected is a float: the same widening inference
   already did on the way in *)
let float d k =
  match req d k with
  | `Float f -> f
  | `Int n -> float_of_int n
  | _ -> failwith (Printf.sprintf "%s: not a number" k)

let opt f d k = match mem d k with None -> None | Some _ -> Some (f d k)
let int_opt d k = opt int d k
let float_opt d k = opt float d k
let string_opt d k = opt string d k
let uuid_opt d k = opt uuid d k
let bool_opt d k = opt bool d k
let unit_opt _ _ = None

(* A member that is itself an object -- one that became its own table. The
   column beside it holds that table's key, so the read descends here first
   and picks the key out of the object rather than reading the member. *)
let obj d k = match mem d k with Some (`Assoc _ as v) -> v | _ -> `Null
let obj_opt = obj

(* The two ways a collection is spelled. An array's elements are positioned by
   an index; a map's entries are keyed by their name, which is why the
   position column is text under a map marking and an integer under an
   array. *)
let arr d k = match mem d k with Some (`List l) -> l | _ -> []
let entries d k = match mem d k with Some (`Assoc kv) -> kv | _ -> []

(* Giving a document an id it did not have.

   A minted key is read twice -- once for the row itself, once for the
   reference column in whatever points at it -- so it cannot be minted at the
   read or the two reads disagree. It is written into the document instead,
   once, before either read happens, and after that a minted key is read
   exactly like one the document always carried. *)
let ensure_id d v =
  match d with
  | `Assoc kv when not (List.mem_assoc "id" kv) -> `Assoc (("id", `String v) :: kv)
  | _ -> d

(* The same, for a member that became a table of its own: the object is
   replaced by one carrying the id, so the reference column beside it and the
   row it points at read the same value. *)
let ensure_member_id d k v =
  match d with
  | `Assoc kv -> (
    match List.assoc_opt k kv with
    | Some (`Assoc _ as o) ->
      `Assoc (List.map (fun (k', v') -> if k' = k then (k', ensure_id o v) else (k', v')) kv)
    | _ -> d)
  | _ -> d
