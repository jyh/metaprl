(*
 * Lists.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *
 *)

include Tacticals

include Itt_equal
include Itt_rfun

open Printf
open Nl_debug
open String_set
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Nl_resource

open Var
open Sequent

open Tacticals
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_list%t" eflush

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
primrw reduce_listindNil :
   list_ind{nil; 'base; h, t, f. 'step['h; 't; 'f]} <--> 'base

primrw reduce_listindCons :
   list_ind{('u :: 'v); 'base; h, t, f. 'step['h; 't; 'f]} <-->
      'step['u; 'v; list_ind{'v; 'base; h, t, f. 'step['h; 't; 'f]}]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_cons
prec prec_list

declare search{'a; 'b}
declare semicolons{'a; 'b}
declare colons{'a; 'b}

(* Empty list *)
dform nil_df : nil = `"[]"

(* Search for nil entry *)
dform cons_df : cons{'a; 'b} =
   search{cons{'a; nil}; 'b}

(* Keep searching down the list *)
dform search_df1 : search{'a; cons{'b; 'c}} =
   search{cons{'b; 'a}; 'c}

(* Found a nil terminator: use bracket notation *)
dform search_df2 : search{'a; nil} =
   `"[" semicolons{'a} `"]"

(* No nil terminator, so use :: notation *)
dform search_df3 : search{'a; 'b} =
   colons{'a} `"::" slot{'b}

(* Reverse entries and separate with ; *)
dform semicolons_df1 : semicolons{cons{'a; nil}} =
   slot{'a}

dform semicolons_df2 : semicolons{cons{'a; 'b}} =
   semicolons{'b} `";" slot{'a}

(* Reverse entries and separate with :: *)
dform colons_df1 : colons{cons{'a; nil}} =
   slot{'a}

dform colons_df2 : colons{cons{'a; 'b}} =
   colons{'b} `"::" slot{'a}

dform list_df1 : mode[prl] :: parens :: "prec"[prec_list] :: list{'a} =
   slot{'a} `" List"

dform list_ind_df1 : mode[prl] :: parens :: "prec"[prec_list] :: list_ind{'e; 'base; h, t, f. 'step} =
   szone pushm[1] pushm[3]
   `"match " slot{'e} `" with" hspace
   `"  [] ->" hspace slot{'base} popm hspace
   `"| " pushm[0] slot{'h} `"::" slot{'t} `"." slot{'f} `" ->" hspace slot{'step} popm popm ezone

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
 * H >- list{A} Type
 * by listType
 * H >- A Type
 *)
prim listType 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{list{'A}} } =
   it

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
 * H >- u1::v1 = u2::v2 in list(A)
 * consEquality
 *
 * H >- u1 = u2 in A
 * H >- v1 = v2 in list(A)
 *)
prim consEquality 'H :
   sequent [squash] { 'H >- 'u1 = 'u2 in 'A } -->
   sequent [squash] { 'H >- 'v1 = 'v2 in list{'A} } -->
   sequent ['ext] { 'H >- cons{'u1; 'v1} = cons{'u2; 'v2} in list{'A} } =
   it

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

(*
 * H >- list(A1) <= list(A2)
 * by listSubtype
 *
 * H >- A1 <= A2
 *)
prim listSubtype 'H :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent ['ext] { 'H >- subtype{list{'A1}; list{'A2}}} =
   it

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let list_term = << list{'A} >>
let list_opname = opname_of_term list_term
let is_list_term = is_dep0_term list_opname
let dest_list = dest_dep0_term list_opname
let mk_list_term = mk_dep0_term list_opname

let nil_term = << nil >>

let cons_term = << cons{'a; 'b} >>
let cons_opname = opname_of_term cons_term
let is_cons_term = is_dep0_dep0_term cons_opname
let dest_cons = dest_dep0_dep0_term cons_opname
let mk_cons_term = mk_dep0_dep0_term cons_opname

let list_ind_term = << list_ind{'e; 'base; h, t, f. 'step['h; 't; 'f]} >>
let list_ind_opname = opname_of_term list_ind_term
let is_list_ind_term = is_dep0_dep0_dep3_term list_ind_opname
let dest_list_ind = dest_dep0_dep0_dep3_term list_ind_opname
let mk_list_ind_term = mk_dep0_dep0_dep3_term list_ind_opname

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

let d_concl_list p =
   nilFormation (hyp_count_addr p) p

let d_hyp_list i p =
   let n, _ = Sequent.nth_hyp p i in
   let j, k = hyp_indices p i in
   let w, u, v = maybe_new_vars3 p "w" "u" "v" in
      (listElimination j k n w u v
       thenLT [addHiddenLabelT "base case";
               addHiddenLabelT "induction step"]) p

let d_listT i =
   if i = 0 then
      d_concl_list
   else
      d_hyp_list i

let d_resource = d_resource.resource_improve d_resource (list_term, d_listT)

let d_list_typeT i p =
   if i = 0 then
      listType (hyp_count_addr p) p
   else
      raise (RefineError ("d_list_typeT", StringError "no elimination form"))

let list_type_term = << "type"{list{'A}} >>

let d_resource = d_resource.resource_improve d_resource (list_type_term, d_list_typeT)

(************************************************************************
 * EQCD TACTICS                                                         *
 ************************************************************************)

(*
 * EqCD list.
 *)
let eqcd_listT p = listEquality (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (list_term, eqcd_listT)

(*
 * EqCD nil.
 *)
let eqcd_nilT p = nilEquality (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (nil_term, eqcd_nilT)

(*
 * EqCD nil.
 *)
let eqcd_consT p = consEquality (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (cons_term, eqcd_consT)

(*
 * EQCD listind.
 *)
let eqcd_list_indT p =
   raise (RefineError ("eqcd_list_indT", StringError "not implemented"))

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (list_ind_term, eqcd_list_indT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of list.
 *)
let inf_list f decl t =
   let a = dest_list t in
      f decl a

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (list_term, inf_list)

(*
 * Type of nil.
 *)
let inf_nil f decl t =
   decl, mk_var_term (new_unify_var decl "T")

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (nil_term, inf_nil)

(*
 * Type of cons.
 *)
let inf_cons inf decl t =
   let hd, tl = dest_cons t in
   let decl', hd' = inf decl hd in
   let decl'', tl' = inf decl' tl in
      unify decl'' StringSet.empty (mk_list_term hd') tl', tl'

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (cons_term, inf_cons)

(*
 * Type of list_ind.
 *)
let inf_list_ind inf decl t =
   let e, base, hd, tl, f, step = dest_list_ind t in
   let decl', e' = inf decl e in
      if is_list_term e' then
         let decl'', base' = inf decl' base in
         let a = dest_list e' in
         let decl''', step' =
            inf (add_unify_subst hd a (**)
                    (add_unify_subst tl e' (**)
                        (add_unify_subst f base' decl'')))
            step
         in
            unify decl''' StringSet.empty base' step', base'
      else
         raise (RefineError ("typeinf", StringTermError ("can't infer type for", t)))

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (list_ind_term, inf_list_ind)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two list types.
 *)
let list_subtypeT p =
   (listSubtype (hyp_count_addr p)
    thenT addHiddenLabelT "subtype") p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (DSubtype ([<< list{'A1} >>, << list{'A2} >>;
               << 'A2 >>, << 'A1 >>],
              list_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
