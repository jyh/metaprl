(*
 * Lists.
 *
 *)

open Debug
open Options
open Resource

include Var

include Itt_equal
include Itt_rfun

(* debug_string DebugLoad "Loading itt_list..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare nil
declare cons{'a; 'b}

declare list{'a}
declare list_ind{'e; 'base; h, t, f. 'step['h; 't; 'f]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Reduction.
 *)
primrw list_indReduceBase :
   list_ind{nil; 'base; h, t, f. 'step['h; 't; 'f]} <--> 'base

primrw list_indReduceStep :
   list_ind{('u :: 'v); 'base; h, t, f. 'step['h; 't; 'f]} <-->
      'step['u; 'v; list_ind{'v; 'base; h, t, f. 'step['h; 't; 'f]}]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform nil = "[" "]"
dform cons{'a; 'b} = slot{'a} `"::" slot{'b}

dform mode[prl] :: list{'a} = slot{'a} `"List"
dform mode[prl] :: list_ind{'e; 'base; h, t, f. 'step['h; 't; 'f]} =
   pushm[1] pushm[3]
   `"case " slot{'e} `" of" space
      nil `" -> " slot{'base} space popm
   `"|" pushm[0]
      slot{'h} `"::" slot{'t} `"." slot{'f} `"->" slot{'step['h; 't; 'f]} popm popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext list(A)
 * by listFormation
 *
 * H >- Ui ext A
 *)
prim listFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   'A

(*
 * H >- list(A) = list(B) in Ui
 * by listEquality
 *
 * H >- A = B in Ui
 *)
prim listEquality 'H :
   sequent [squash] { 'H >- 'A = 'B in univ[@i:l] } -->
   sequent ['ext] { 'H >- list{'A} = list{'B} in univ[@i:l] } =
   it

(*
 * H >- list(A) ext nil
 * by nilFormation
 *
 * H >- A = A in Ui
 *)
prim nilFormation 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- 'A list } =
   nil

(*
 * H >- nil = nil in list(A)
 * by nilEquality
 *
 * H >- A = A in Ui
 *)
prim nilEquality 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- nil = nil in list{'A} } =
   it

(*
 * H >- list(A) ext cons(h; t)
 * by consFormation
 *
 * H >- A ext h
 * H >- list(A) ext t
 *)
prim consFormation 'H :
   ('h : sequent ['ext] { 'H >- 'A }) -->
   ('t : sequent ['ext] { 'H >- list{'A} }) -->
   sequent ['ext] { 'H >- list{'A} } =
   'h :: 't

(*
 * H; l: list(A); J[l] >- C[l]
 * by listElimination w u v
 *
 * H; l: list(A); J[l] >- C[nil]
 * H; l: list(A); J[l]; u: A; v: list(A); w: C[v] >- C[u::v]
 *)
prim listElimination 'H 'J 'l 'w 'u 'v :
   ('base['l] : sequent ['ext] { 'H; l: list{'A}; 'J['l] >- 'C[nil] }) -->
   ('step['l; 'u; 'v; 'w] : sequent ['ext] { 'H; l: list{'A}; 'J['l]; u: 'A; v: list{'A}; w: 'C['v] >- 'C['u::'v] }) -->
   sequent ['ext] { 'H; l: list{'A}; 'J['l] >- 'C['l] } =
   list_ind{'l; 'base['l]; u, v, w. 'step['l; 'u; 'v; 'w]}

(*
 * H >- rec_case(e1; base1; u1, v1, z1. step1[u1; v1]
 *      = rec_case(e2; base2; u2, v2, z2. step2[u2; v2]
 *      in T[e1]
 *
 * by list_indEquality lambda(r. T[r]) list(A) u v w
 *
 * H >- e1 = e2 in list(A)
 * H >- base1 = base2 in T[nil]
 * H, u: A; v: list(A); w: T[v] >- step1[u; v; w] = step2[u; v; w] in T[u::v]
 *)
prim list_indEquality 'H lambda{l. 'T['l]} list{'A} 'u 'v 'w :
   sequent [squash] { 'H >- 'e1 = 'e2 in list{'A} } -->
   sequent [squash] { 'H >- 'base1 = 'base2 in 'T[nil] } -->
   sequent [squash] { 'H; u: 'A; v: list{'A}; w: 'T['v] >-
             'step1['u; 'v; 'w] = 'step2['u; 'v; 'w] in 'T['u::'v]
           } -->
   sequent ['ext] { 'H >- list_ind{'e1; 'base1; u1, v1, z1. 'step1['u1; 'v1; 'z1]}
                   = list_ind{'e2; 'base2; u2, v2, z2. 'step2['u2; 'v2; 'z2]}
                   in 'T['e1]
           } =
   it
   
(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)
     
(*
 * D
 *)
let list_term = << list{'A} >>
let nil_term = << nil >>
let cons_term = << cons{'a; 'b} >>

let d_concl_list p =
   nilFormation (hyp_count p) p

let d_hyp_list i p =
   let count = hyp_count p in
   let i' = get_pos_hyp_index i count in
   let n = var_of_hyp i' p in
      (match maybe_new_vars ["w"; "u"; "v"] (declared_vars p) with
          [w; u; v] ->
             listElimination i' (count - i' - 1) n w u v
             thenLT [addHiddenLabelT "base case";
                     addHiddenLabelT "induction step"]
        | _ ->
             failT) p

let d_list i =
   if i = 0 then
      d_concl_list
   else
      d_hyp_list i

let d_resource = d_resource.resource_improve d_resource (list_term, d_list)
let d = d_resource.resource_extract d_resource

(*
 * EqCD.
 *)
let eqcd_list p = listEquality (hyp_count p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (list_term, eqcd_list)
let eqcd = eqcd_resource.resource_extract eqcd_resource

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:52:16  jyh
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
 * Revision 1.4  1996/10/23 15:18:09  jyh
 * First working version of dT tactic.
 *
 * Revision 1.3  1996/05/21 02:16:54  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:04  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/30 01:37:15  jyh
 * Initial version of ITT.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
