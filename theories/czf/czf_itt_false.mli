(*
 * Logical false.
 *)

include Czf_itt_set

open Tacticals

declare "false"

(*
 * Empty type.
 *)
rewrite unfoldFalse : "false" <--> (0 = 1 in int)

(*
 * From false prove anything.
 *
 * H, x: false, J >> T
 * by false_elim i
 *)
axiom false_elim 'H 'J :
   sequent ['ext] { 'H; x: "false"; 'J['x] >- 'T['x] }

(*
 * False is well-formed.
 *)
axiom false_wf 'H :
   sequent ['ext] { 'H >- wf{."false"} }

(*
 * False is a restricted formula.
 *)
axiom false_res 'H :
   sequent ['ext] { 'H >- restricted{."false"} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
