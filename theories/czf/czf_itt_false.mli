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
 * $Log$
 * Revision 1.3  1998/07/02 18:37:08  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
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
