(*
 * Logical false.
 *)

include Czf_itt_wf

open Tactic_type

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
 * $Log$
 * Revision 1.2  1998/06/16 16:25:59  jyh
 * Added itt_test.
 *
 * Revision 1.1  1998/06/15 22:32:47  jyh
 * Added CZF.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
