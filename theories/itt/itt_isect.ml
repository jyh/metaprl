(*
 * Intersection type.
 *
 *)

open Debug
open Options
open Resource

include Var

include Itt_equal
include Itt_set
include Itt_rfun

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

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_isect p =
   let count = hyp_count p in
   let y = get_opt_var_arg "y" p in
      (intersectionMemberFormation count y
       thenLT [addHiddenLabelT "wf";
               idT]) p

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
let d_isect i =
   if i = 0 then
      d_concl_isect
   else
      d_hyp_isect i

let isect_term = << isect x: 'A. 'B['x] >>

let d_resource = d_resource.resource_improve d_resource (isect_term, d_isect)
let d = d_resource.resource_extract d_resource

(*
 * EQCD.
 *)
let eqcd_isect p =
   let count = hyp_count p in
   let v = get_opt_var_arg "y" p in
      (intersectionEquality count v
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (isect_term, eqcd_isect)
let eqcd = eqcd_resource.resource_extract eqcd_resource

(*
 * $Log$
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
