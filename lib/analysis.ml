type filter =
  | Keep_all
  | Int_compare of {
      column : string;
      op : Query.op;
      operand : int;
      guarded : bool;
    }
  | Float_compare of {
      column : string;
      op : Query.op;
      operand : float;
      guarded : bool;
    }
  | Text_compare of {
      column : string;
      op : Query.op;
      operand : string;
      guarded : bool;
    }

type project =
  (*NOTE Gather allocated a fresh array and copied every element to produce something identical *)
  (*     Identity means nothing to gather as it is every row is surviving *)
  | Identity of string list
  | Gather of string list

type t = {
  read : string list;
  filter : filter;
  project : project;
}
