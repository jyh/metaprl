(*
 * Logical false.
 *)

include Czf_itt_set

open Refiner.Refiner.RefineError

open Sequent
open Resource
open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "false"

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform false_df : "false" =
   `"false'"

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

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let false_term = << "false" >>
let wf_false_term = << wf{."false"} >>
let res_false_term = << restricted{."false"} >>

(*
 * Falsehood.
 *)
let d_falseT i p =
   (if i = 0 then
      idT
   else
      let i, j = hyp_indices p i in
         false_elim i j) p

let d_resource = d_resource.resource_improve d_resource (false_term, d_falseT)

(*
 * Well-formedness.
 *)
let d_wf_falseT i p =
   if i = 0 then
      false_wf (hyp_count p) p
   else
      raise (RefineError ("d_wf_falseT", (StringTermError ("no elim form", wf_false_term))))

let d_resource = d_resource.resource_improve d_resource (wf_false_term, d_wf_falseT)

(*
 * Restricted.
 *)
let d_res_falseT i p =
   if i = 0 then
      false_res (hyp_count p) p
   else
      raise (RefineError ("d_res_falseT", (StringTermError ("no elim form", res_false_term))))

let d_resource = d_resource.resource_improve d_resource (res_false_term, d_res_falseT)

(*
 * $Log$
 * Revision 1.4  1998/07/02 18:37:07  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.3  1998/07/01 04:37:24  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.2  1998/06/16 16:25:58  jyh
 * Added itt_test.
 *
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

