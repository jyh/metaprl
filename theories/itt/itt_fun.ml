(*
 * Simplifications for undependent functions.
 *
 *)

include Tactic_type

include Itt_equal
include Itt_rfun

open Printf
open Debug
open Refiner.Refiner.Term
open Options
open Resource
open Refine_sig

open Sequent
open Tacticals
open Itt_equal
open Itt_subtype
open Itt_rfun

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_fun%t" eflush

(* debug_string DebugLoad "Loading itt_fun..." *)

(*
 * H >- Ui ext A -> B
 * by independentFunctionFormation
 *
 * H >- Ui ext A
 * H >- Ui ext B
 *)
prim independentFunctionFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[@i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   'A -> 'B

(*
 * H >- (A1 -> B1) = (A2 -> B2) in Ui
 * by independentFunctionEquality
 *
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
prim independentFunctionEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- ('A1 -> 'B1) = ('A2 -> 'B2) in univ[@i:l] } =
   it

(*
 * H >- a:A -> B[a] ext lambda(z. b[z])
 * by lambdaFormation Ui z
 *
 * H >- A = A in Ui
 * H, z: A >- B[z] ext b[z]
 *)
prim independentLambdaFormation 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   ('b['z] : sequent ['ext] { 'H; z: 'A >- 'B }) -->
   sequent ['ext] { 'H >- 'A -> 'B } =
   lambda{z. 'b['z]}

(*
 * H, f: A -> B, J[x] >- T[x]                   ext t[f, f a]
 * by independentFunctionElimination i y
 *
 * H, f: A -> B, J >- A                         ext a
 * H, f: A -> B, J[x], y: B >- T[x]             ext t[f, y]
 *)
prim independentFunctionElimination 'H 'J 'f 'y :
   ('a : sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'A }) -->
   ('t['f; 'y] : sequent ['ext] { 'H; f: 'A -> 'B; 'J['f]; y: 'B >- 'T['f] }) -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'T['f] } =
   't['f; 'f 'a]

(*
 * H >- A1 -> B1 <= A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H >- B1 <= B2
 *)
prim independentFunctionSubtype 'H :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 -> 'B1); ('A2 -> 'B2) } } =
   it

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_fun p =
   let count = hyp_count p in
   let z = get_opt_var_arg "z" p in
      (independentLambdaFormation count z
       thenLT [addHiddenLabelT "w"; idT]) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_fun i p =
   let count = hyp_count p in
   let i' = get_pos_hyp_index i count in
   let f = var_of_hyp i' p in
   let y = get_opt_var_arg "y" p in
      independentFunctionElimination i' (count - i' - 1) f y p

(*
 * Join them.
 *)
let d_funT i =
   if i = 0 then
      d_concl_fun
   else
      d_hyp_fun i

let d_resource = d_resource.resource_improve d_resource (fun_term, d_funT)

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

(*
 * EQCD.
 *
 * Need a term for the well-order.
 *)
let eqcd_funT p =
   let count = hyp_count p in
      (independentFunctionEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (fun_term, eqcd_funT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_fun f decl t =
   let a, b = dest_fun t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
   let le1, le2 =
      try dest_univ a', dest_univ b' with
         Term.TermMatch _ -> raise (RefineError (StringTermError ("typeinf: can't infer type for", t)))
   in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (fun_term, inf_fun)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let fun_subtypeT p =
   (independentFunctionSubtype (hyp_count p)
    thenT addHiddenLabelT "subtype") p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (DSubtype ([<< 'A1 -> 'B1 >>, << 'A2 -> 'B2 >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1 >>, << 'B2 >>],
              fun_subtypeT))

(*
 * $Log$
 * Revision 1.6  1998/05/28 13:47:36  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.5  1998/04/24 02:43:29  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.4  1998/04/22 22:44:45  jyh
 * *** empty log message ***
 *
 * Revision 1.3  1998/04/09 18:26:04  jyh
 * Working compiler once again.
 *
 * Revision 1.2  1997/08/06 16:18:30  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:11  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.4  1996/10/23 15:18:07  jyh
 * First working version of dT tactic.
 *
 * Revision 1.3  1996/05/21 02:16:46  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:33:59  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/28 02:51:30  jyh
 * This is an initial version of the type theory.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
