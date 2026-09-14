(* Every table's key type, so a foreign key can be named without depending
   on the module it points into.  This is what keeps xs.mli from having to
   mention Root, which is what would otherwise make the two files cyclic. *)
type xs
type b
type root
