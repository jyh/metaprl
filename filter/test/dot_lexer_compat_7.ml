(* camlp5 7: the reference lexer, as camlp5 7's pa_o made it. *)
let make () =
   Plexer.dollar_for_antiquotation := true;
   Plexer.gmake ()

let lookup loc i = loc i
