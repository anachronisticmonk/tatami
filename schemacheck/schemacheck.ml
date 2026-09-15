let () =
  let dir = Sys.argv.(1) in
  Tatami.Schema.load_dir dir
  |> List.iter (fun (t : Tatami.Schema.t) ->
         Printf.printf "%s\n" t.table;
         List.iter
           (fun (c : Tatami.Schema.column) ->
             Printf.printf "    %-18s %-16s %s\n" c.name
               (Tatami.Schema.layout_to_string c.layout)
               (match c.refers_to with
                | Some x -> "-> " ^ x
                | None -> ""))
           t.columns)
