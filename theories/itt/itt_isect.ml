(*
 * Intersection type.
 *
 *)

include Tacticals

include Itt_equal
include Itt_set
include Itt_rfun

open Printf
open Nl_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Resource

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

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "isect"{'A; x. 'B['x]}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform isect_df1 : mode[prl] :: (isect x: 'A. 'B['x]) = cap slot{'x} `":" slot{'A} `"." slot{'B['x]}
dform isect_df2 : mode[src] :: (isect x: 'A. 'B['x]) = `"isect " slot{'x} `":" slot{'A} `"." slot{'B['x]}

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
   raise (RefineError ("d_concl_isect", StringError "no rule for intersectionFormation"))

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_isect i p =
   let a = get_with_arg p in
   let i, j = hyp_indices p i in
   let x, _ = Sequent.nth_hyp p i in
      (match maybe_new_vars ["y"; "v"] (declared_vars p) with
          [y; v] ->
             intersectionElimination i j a x y v
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
   let le1, le2 = dest_univ a', dest_univ b' in
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
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
