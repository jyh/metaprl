(* The expressions bound by a top-level let, for camlp5 7's MLast. *)
let let_exprs = function
   MLast.StVal (_, _, Ploc.VaVal pel) -> Some (List.map snd pel)
 | _ -> None
