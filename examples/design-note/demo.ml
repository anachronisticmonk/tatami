(* Walks the generated modules, which is how the design note says a document
   is reconstructed: start at a Root.t and call accessors down into the
   children. *)

open Generated

let () =
  match Root.all () with
  | [] -> print_endline "no documents"
  | r :: _ ->
      (* r : Root.t *)
      Printf.printf "Root.a          = %d\n" r.Root.a;

      (* r.Root.b : B.id -- an opaque key. You cannot print it or compare it;
         the only thing it is good for is being followed. *)
      let child : B.t = Root.b r in
      Printf.printf "Root.b -> B.c   = %d\n" child.B.c;
      Printf.printf "Root.b -> B.d   = %d\n" child.B.d;

      (* which is the original document again *)
      Printf.printf "\nreconstructed   = { \"a\": %d, \"b\": { \"c\": %d, \"d\": %d } }\n"
        r.Root.a child.B.c child.B.d;

      (* entry by an outside key, which may name nothing *)
      print_newline ();
      List.iter
        (fun k ->
          match Root.find k with
          | Some row -> Printf.printf "Root.find %d      = a = %d\n" k row.Root.a
          | None     -> Printf.printf "Root.find %d      = None\n" k)
        [ 1; 99 ]
