(*
 * Logical false.
 *)

include Czf_itt_wf

open Resource
open Tactic_type

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "false"

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform false_df : "false" =
   `"false"

(************************************************************************
 * DEFINTION                                                            *
 ************************************************************************)

primrw unfoldFalse : "false" <--> (0 = 1 in int)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * From false prove anything.
 *
 * H, x: false, J >> T
 * by false_elim i
 *)
prim false_elim 'H 'J : :
   sequent ['ext] { 'H; x: "false"; 'J['x] >- 'T['x] } =
   it

(*
 * False is well-formed.
 *)
prim false_wf 'H : :
   sequent ['ext] { 'H >- wf{."false"} } =
   it

(*
 * False is a restricted formula.
 *)
prim false_res 'H : :
   sequent ['ext] { 'H >- restricted{."false"} } =
   it

let dT = d_resource.resource_extract d_resource

(*
 * $Log$
 * Revision 1.1  1998/06/15 22:32:46  jyh
 * Added CZF.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
