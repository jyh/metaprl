(*
 * Logical true.
 *)

include Czf_itt_sep

(*
 * True is functional.
 *)
axiom unit_fun 'H :
   sequent ['ext] { 'H >- fun_prop{z. "unit"} }

(*
 * True is a restricted formula.
 *)
axiom unit_res 'H :
   sequent ['ext] { 'H >- restricted{z. "unit"} }

(*
 * True is functional.
 *)
axiom true_fun 'H :
   sequent ['ext] { 'H >- fun_prop{z. "true"} }

(*
 * True is a restricted formula.
 *)
axiom true_res 'H :
   sequent ['ext] { 'H >- restricted{z. "true"} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
