(* An id for a document that carries none.

   Called by the engine, not by the generated loaders: the point at which a key
   is created has to be the point before anything reads it, and that is the
   walk. See [Json.ensure_id]. *)

let counter = ref 0

let uuid () =
  incr counter;
  Printf.sprintf "00000000-0000-4000-8000-%012x" !counter
