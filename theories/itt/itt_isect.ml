(*
 * Intersection type.
 *
 *)

include Tactic_type

include Itt_equal
include Itt_set
include Itt_rfun

open Printf
open Debug
open Refiner.Refiner.Term
open Options
open Resource
open Refine_sig

open Var
open Sequent
open Tacticals
open Itt_equal
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_isect%t" eflush

(* debug_string DebugLoad "Loading itt_isect..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "isect"{'A; x. 'B['x]}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform mode[prl] :: (isect x: 'A. 'B['x]) = cap slot{'x} `":" slot{'A} `"." slot{'B['x]}
dform mode[src] :: (isect x: 'A. 'B['x]) = `"isect " slot{'x} `":" slot{'A} `"." slot{'B['x]}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext isect x: A. B[x]
 * by intersectionFormation x A
 * H >- A = A in Ui
 * H, x: A >- Ui ext B[x]
 *)
prim intersectionFormation 'H 'x 'A :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   ('B['x] : sequent ['ext] { 'H; x: 'A >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   isect x: 'A. 'B['x]

(*
 * H >- isect x1:A1. B1[x1] = isect x2:A2. B2[x2] in Ui
 * by intersectionEquality y
 * H >- A1 = A2 in Ui
 * H, y: A1 >- B1[y] = B2[y] in Ui
 *)
prim intersectionEquality 'H 'y :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[@i:l] } -->
   sequent ['ext] { 'H >- isect x1: 'A1. 'B1['x1] = isect x2: 'A2. 'B2['x2] in univ[@i:l] } =
   it

(*
 * H >- isect x: A. B[x] ext b[it]
 * by intersectionMemberFormation z
 * H >- A = A in type
 * H, z: hide(A) >- B[z] ext b[z]
 *)
prim intersectionMemberFormation 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   ('b['z] : sequent ['ext] { 'H; z: hide('A) >- 'B['z] }) -->
   sequent ['ext] { 'H >- isect x: 'A. 'B['x] } =
   'b[it]

(*
 * H >- b1 = b2 in isect x:A. B[x]
 * by intersectionMemberEquality z
 * H >- A = A in type
 * H, z: A >- b1 = b2 in B[z]
 *)
prim intersectionMemberEquality 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; z: 'A >- 'b1 = 'b2 in 'B['z] } -->
   sequent ['ext] { 'H >- 'b1 = 'b2 in isect x: 'A. 'B['x] } =
   it

(*
 * H >- b1 = b2 in B[a]
 * by intersectionMemberCaseEquality (isect x:A. B[x]) a
 * H >- b1 = b2 in isect x:A. B[x]
 * H >- a = a in A
 *)
prim intersectionMemberCaseEquality 'H (isect x: 'A. 'B['x]) 'a :
   sequent [squash] { 'H >- 'b1 = 'b2 in isect x: 'A. 'B['x] } -->
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'b1 = 'b2 in 'B['a] } =
   it

(*
 * H, x: isect y: A. B[y], J[x] >- T[x] ext t[x, x, it]
 * by intersectionElimination a z v
 * H, x: isect y: A. B[y], J[x] >- a = a in A
 * H, x: isect y: A. B[y], J[x], z: B[a], v: z = f in B[a] >- T[x] ext t[x, y, z]
 *)
prim intersectionElimination 'H 'J 'a 'x 'y 'v :
   sequent [squash] { 'H; x: isect y: 'A. 'B['y]; 'J['x] >- 'a = 'a in 'A } -->
   ('t['x; 'y; 'v] : sequent ['ext] { 'H; x: isect y: 'A. 'B['y]; 'J['x]; z: 'B['a]; v: 'z = 'x in 'B['a] >- 'T['x] }) -->
   sequent ['ext] { 'H; x: isect y: 'A. 'B['y]; 'J['x] >- 'T['x] } =
   't['x; 'x; it]

(*
 * H >- isect a1:A1. B1 <= isect a2:A2. B2
 * by intersectionSubtype
 *
 * H >- A2 <= A1
 * H, a: A1 >- B1[a] <= B2[a]
 *)
prim intersectionSubtype 'H 'a :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { 'H >- subtype{ (isect a1:'A1. 'B1['a1]); (isect a2:'A2. 'B2['a2]) } } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let isect_term = << isect x: 'A. 'B['x] >>
let isect_opname = opname_of_term isect_term
let is_isect_term = is_dep0_dep1_term isect_opname
let dest_isect = dest_dep0_dep1_term isect_opname
let mk_isect_term = mk_dep0_dep1_term isect_opname

(*
 * D the conclusion.
 *)
let d_concl_isect p =
   raise (RefineError (StringError "d_concl_isect: no rule for intersectionFormation"))

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_isect i p =
   let a = get_term_arg 0 p in
   let count = hyp_count p in
   let i' = get_pos_hyp_index i count in
   let x = var_of_hyp i' p in
      (match maybe_new_vars ["y"; "v"] (declared_vars p) with
          [y; v] ->
             intersectionElimination i' (count - i' - 1) a x y v
        | _ ->
             failT) p

(*
 * Join them.
 *)
let d_isectT i =
   if i = 0 then
      d_concl_isect
   else
      d_hyp_isect i

let d_resource = d_resource.resource_improve d_resource (isect_term, d_isectT)

(*
 * EQCD.
 *)
let eqcd_isectT p =
   let count = hyp_count p in
   let v = get_opt_var_arg "y" p in
      (intersectionEquality count v
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (isect_term, eqcd_isectT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of isect.
 *)
let inf_isect f decl t =
   let v, a, b = dest_isect t in
   let decl', a' = f decl a in
   let decl'', b' = f ((v, a)::decl') b in
   let le1, le2 =
      try dest_univ a', dest_univ b' with
         Term.TermMatch _ -> raise (RefineError (StringTermError ("typeinf: can't infer type for", t)))
   in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (isect_term, inf_isect)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two intersection types.
 *)
let isect_subtypeT p =
   let a = get_opt_var_arg "x" p in
      (intersectionSubtype (hyp_count p) a
       thenT addHiddenLabelT "subtype") p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (DSubtype ([<< isect a1:'A1. 'B1['a1] >>, << isect a2:'A2. 'B2['a2] >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              isect_subtypeT))

(*
 * $Log$
 * Revision 1.6  1998/05/28 13:47:40  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.5  1998/04/24 02:43:32  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.4  1998/04/22 22:44:51  jyh
 * *** empty log message ***
 *
 * Revision 1.3  1998/04/09 18:26:06  jyh
 * Working compiler once again.
 *
 * Revision 1.2  1997/08/06 16:18:32  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:14  jyh
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
 * Revision 1.3  1996/10/23 15:18:08  jyh
 * First working version of dT tactic.
 *
 * Revision 1.2  1996/05/21 02:16:52  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.1  1996/03/30 01:37:14  jyh
 * Initial version of ITT.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
