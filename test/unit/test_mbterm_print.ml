(* unit-link: filter *)
(* Mbterm.print_term (library/mbterm.ml), the Nuprl-5 link's debug
   printer of a term, and its print_subterms and print_param, which no
   unit test, theory build or proof census reached (2026-11-15 rank).
   Each line is one term's printing (stdout), from a constant to two
   bindings, and every kind of parameter the printer takes; a Quote is
   refused (as the code says).
   The expected file is the output of the code as written (2026-11-15),
   never typed. *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermType

let v = Lm_symbol.add
let op s ps = mk_op (Opname.make_opname [ s; "Test" ]) ps
let c = mk_term (op "c" []) []

let show name t =
  print_string (name ^ ": ");
  (try Mbterm.print_term t with e -> print_string ("raised " ^ Printexc.to_string e));
  print_newline ()

let () =
  show "constant" c;
  show "one subterm" (mk_term (op "f" []) [ mk_bterm [] c ]);
  show "two subterms" (mk_term (op "g" []) [ mk_bterm [] c; mk_bterm [] (mk_term (op "f" []) [ mk_bterm [] c ]) ]);
  show "a binding" (mk_term (op "lam" []) [ mk_bterm [ v "x" ] (mk_var_term (v "x")) ]);
  show "two bindings" (mk_term (op "k" []) [ mk_bterm [ v "x"; v "y" ] c ]);
  show "parameters" (mk_term (op "p" [ make_param (Number (Lm_num.num_of_int 3)); make_param (String "s");
                                       make_param (Token (Opname.make_opname [ "t" ])); make_param (Var (v "x"));
                                       make_param (MNumber (v "n")); make_param (MString (v "m")); make_param (MToken (v "q"));
                                       make_param (MLevel (mk_level 1 [ mk_level_var (v "i") 2 ]));
                                       make_param (ParamList [ make_param (Number (Lm_num.num_of_int 1)) ]) ]) []);
  show "a quote" (mk_term (op "q" [ make_param Quote ]) [])
