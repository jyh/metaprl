(*
 * OCaml expressions.
 *)

(*
 * Record projection.
 *)
declare proj[$start:n; $finish:n]{'e1; 'e2}

dform mode[prl] :: proj[$start:n; $finish:n]{'e1; 'e2} =
   slot{'e1} `"." slot{'e2}

(*
 * Application.
 *)
declare apply[$start:n; $finish:n]{'e1; 'e2}

dform mode[prl] :: apply[$start:n; $finish:n]{'e1; 'e2} =
   slot{'e1} space slot{'e2}

(*
 * Array subscript.
 *)
declare array_subscript[$start:n; $finish:n]{'e1; 'e2}

dform mode[prl] :: array_subscript[$start:n; $finish:n]{'e1; 'e2} =
   slot{'e1} `".(" slot{'e2} `")"

(*
 * Array construction.
 * Arrays are terminated lists.
 *)
declare array[$start:n; $finish:n]{'a}

dform mode[prl] :: array[$start:n; $finish:n]{'a} =
   `"[|" list_cons{'a} `"|]"

(*
 * Assignment.
 *)
declare assign[$start:n; $finish:n]{'e1; 'e2}
           
dform mode[prl] :: assign[$start:n; $finish:n]{'e1; 'e2} =
   slot{'e1} `":=" slot{'e2}

(*
 * Character constant.
 *)
declare char[$start:n; $finish:n; $c:s]

(*
 * Class coercion.
 *)
declare coerce[$start:n; $finish:n]{'e; 't}

dform mode[prl] :: coerce[$start:n; $finish:n]{'e; 't} =
   slot{'e} `":>" slot{'t}

(*
 * Floating point constant.
 *)
declare float[$start:n; $finish:n; $f:s]

(*
 * For loop.
 *)
declare for_upto[$start:n; $finish:n]{'s; 't; v. 'body]

dform mode[prl] :: for_upto[$start:n; $finish:n]{'s; 't; v. 'body] =
   `"for" slot{'v} `" := " slot{'s} `" to " slot{'t} `" do " sbreak slot{'body} sbreak `"done"

declare for_downto[$start:n; $finish:n]{'s; 't; v. 'body]

dform mode[prl] :: for_downto[$start:n; $finish:n]{'s; 't; v. 'body] =
   `"for" slot{'v} `" := " slot{'s} `" downto " slot{'t} `" do " sbreak slot{'body} sbreak `"done"

(*
 * Function.
 * Argument is a pwe.
 *)
declare lambda_pattern[$start:n; $finish:n]{'a}

dform mode[prl] :: lambda_pattern[$start:n; $finish:n]{'a} =
   df_pwe{'a}

(*
 * Conditional.
 *)
declare if[$start:n; $finish:n]{'e1; 'e2; 'e3}
          
dform mode[prl] :: if[$start:n; $finish:n]{'e1; 'e2; 'e3} =
   `"if" slot{'e1} `" then" break slot{'e2} break `"else" break slot{'e3}
                     
(*
 * Integer constant.
 *)
declare int[$start:n; $finish:n; $i:n]

dform mode[prl] :: int[$start:n; $finish:n; $i:n] =
   int[$i:n]

(*
 * Let binding.
 *)
declare letrec{
(*
 * $Log$
 * Revision 1.1  1998/01/03 23:20:25  jyh
 * Upgraded to OCaml 1.07, initial semantics of OCaml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
