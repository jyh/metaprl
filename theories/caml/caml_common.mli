(*
 * Miscelleneous constructions.
 *)

include Caml_base

(*
 * Generic list construction.
 *)
declare cons{'car; 'cdr}

declare nil{}

declare df_cons{'a}

dform mode[prl] :: df_cons{nil} = `""

dform mode[prl] :: df_cons{cons{'a; nil}} =
   slot{'a}

dform mode[prl] :: df_cons{cons{'a; 'b}} =
   slot{'a} `";" space df_cons{'b}

(*
 * Pattern, with -expression, and expression.
 *)
declare pwe{'p; 'w; 'e}

declare df_pwe{'a}

dform mode[prl] :: pwe{'p; 'w; 'e} =
   slot{'p} `" with " slot{'w} `" -> " slot{'e}

dform mode[prl] :: df_pwe{nil} = `""

dform mode[prl] :: df_pwe{cons{'a; nil}} =
   slot{'a}

dform mode[prl] :: df_pwe{cons{'a; 'b}} =
   slot{'a} break `"| " df_pwe{'b}

(*
 * $Log$
 * Revision 1.1  1998/01/03 23:20:24  jyh
 * Upgraded to OCaml 1.07, initial semantics of OCaml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
