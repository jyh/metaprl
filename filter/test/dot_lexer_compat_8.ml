(* camlp5 8: the lexer filter_parse installs. *)
let make () =
   Plexer.simplest_raw_strings := false;
   Plexer.dollar_for_antiquotation := true;
   Filter_dot_lexer.split (Plexer.gmake ())

let lookup = Plexing.Locations.lookup
