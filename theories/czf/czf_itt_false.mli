(*
 * Logical false.
 *)

include Czf_itt_sep

open Tacticals

(*
 * False is a restricted formula.
 *)
axiom void_fun 'H :
   sequent ['ext] { 'H >- fun_prop{x ."void"} }

(*
 * False is a restricted formula.
 *)
axiom void_res 'H :
   sequent ['ext] { 'H >- restricted{x ."void"} }

(*
 * False is a restricted formula.
 *)
axiom false_fun 'H :
   sequent ['ext] { 'H >- fun_prop{x ."false"} }

(*
 * False is a restricted formula.
 *)
axiom false_res 'H :
   sequent ['ext] { 'H >- restricted{x ."false"} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
