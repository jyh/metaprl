(*
 * Subtype type.
 *
 *)

open Debug
open Options
open Resource

open Var
     
include Itt_equal
include Itt_logic

(* debug_string DebugLoad "Loading itt_subtype..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare subtype{'A; 'B}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

declare ext_equal{'A; 'B}
primrw ext_equal : ext_equal{'A; 'B} <--> subtype{'A; 'B} & subtype{'B; 'A}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform mode[prl] :: subtype{'A; 'B} = slot{'A} subseteq slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext subtype(A; B)
 * by subtypeFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
prim subtypeFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[@i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   subtype{'A; 'B}

(*
 * H >- subtype(A1; B1) = subtype(A2; B2) in Ui
 * by subtypeEquality
 *
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
prim subtypeEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- subtype{'A1; 'B1} = subtype{'A2; 'B2} in univ[@i:l] } =
   it

(*
 * H >- subtype(A; B) ext it
 * by subtype_axiomFormation
 *
 * H >- A = A in Ui
 * H; x: A; y: A; x = y in A >- x = y in B
 *)
prim subtype_axiomFormation 'H 'x 'y 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'A; y: 'A; z: 'x = 'y in 'A >- 'x = 'y in 'B } -->
   sequent ['ext] { 'H >- subtype{'A; 'B} } =
   it

(*
 * H >- it = it in subtype(A; B)
 * by subtype_axiomEquality
 *
 * H >- subtype(A; B)
 *)
prim subtype_axiomEquality 'H :
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- it = it in subtype{'A; 'B} } =
   it

(*
 * H, x: subtype(A; B); J[x] >- C[x]
 * by subtypeElimination
 *
 * H, x: subtype(A; B); J[it] >- C[it]
 *)
prim subtypeElimination 'H 'J :
   ('t : sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J['x] >- 'C['x] } =
   't

(*
 * H >- x = y in B
 * by subtypeElimination2 A
 *
 * H >- x = y in A
 * H >- subtype(A; B)
 *)
prim subtypeElimination2 'H 'A :
   sequent [squash] { 'H >- 'x = 'y in 'A } -->
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- 'x = 'y in 'B } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_subtype p =
   let count = hyp_count p in
      (match maybe_new_vars ["x"; "y"; "%z"] (declared_vars p) with
          [x; y; z] ->
             subtype_axiomFormation count x y z
             thenLT [addHiddenLabelT "wf";
                     addHiddenLabelT "aux"]
        | _ -> failT) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_subtype i p =
   let count = hyp_count p in
   let i' = get_pos_hyp_index i count in
      subtypeElimination i' (count - i' - 1) p

(*
 * Join them.
 *)
let d_subtype i =
   if i = 0 then
      d_concl_subtype
   else
      d_hyp_subtype i

let subtype_term = << subtype{'A; 'B} >>

let d_resource = d_resource.resource_improve d_resource (subtype_term, d_subtype)
let d = d_resource.resource_extract d_resource

(*
 * EQCD.
 *)
let eqcd_subtype p =
   let count = hyp_count p in
      (subtypeEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (subtype_term, eqcd_subtype)
let eqcd = eqcd_resource.resource_extract eqcd_resource

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:52:29  jyh
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
 * Revision 1.4  1996/10/23 15:18:12  jyh
 * First working version of dT tactic.
 *
 * Revision 1.3  1996/05/21 02:17:18  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:21  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/30 01:37:21  jyh
 * Initial version of ITT.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
