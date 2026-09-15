(* What a derived column holds between [make] and the setter that stamps it.

   None of these reaches the database: every column built with one is
   overwritten by a setter before the getters read the row back out. They
   exist because [make] is total -- it takes every column -- while the
   document supplies only some. *)

let int = 0
let float = 0.
let string = ""
let uuid = ""
let bool = false
let unit = ()
