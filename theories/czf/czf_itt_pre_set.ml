(*
 * The "set" type is used to relate CZF to the Nuprl type theory.
 * The set type is defined inductively.
 *    The base types are:
 *       1. int
 *       2. fun{A; x.B[x]}
 *       3. exists{A; x.B[x]}
 *       4. union{A; B}
 *       5. equal{A; a; b}
 *
 *    The inductive construction is given by rule:
 *       6. H >- T in U1         H, x:T >- a in set
 *          -------------------------------------
 *               H >- collect{T; x. a[x]} in set
 *
 * We could define this set recursively.  Instead, we define it
 * as a collection of rules.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
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
 *)

include Itt_theory

open Printf
open Mp_debug

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Term_stable

open Tacticals
open Tacticals
open Conversionals
open Sequent
open Var

open Base_dtactic
open Base_auto_tactic

open Itt_squash
open Itt_equal
open Itt_rfun
open Itt_dprod
open Itt_union
open Itt_struct
open Itt_logic
open Itt_w

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_pre_set%t" eflush

let debug_czf_set =
   create_debug (**)
      { debug_name = "czf_set";
        debug_description = "display czf_set operations";
        debug_value = false
      }

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Sets are built by collecting over small types.
 *   set: the type of all sets
 *   is_pre_set{'s}: the judgement that 's is a set
 *   collect{'T; x. 'a['x]}:
 *      the set constructed from the family of sets 'a['x]
 *      where 'x ranges over 'T
 *   set_ind is the induction combinator.
 *)
declare pre_set
declare is_pre_set{'s}
declare collect{'T; x. 'a['x]}
declare set_ind{'s; x, f, g. 'b['x; 'f; 'g]}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Sets.
 *)
primrw unfold_pre_set : pre_set <--> w{univ[1:l]; x. 'x}
primrw unfold_is_pre_set : is_pre_set{'s} <--> ('s = 's in pre_set)
primrw unfold_collect : collect{'T; x. 'a['x]} <--> tree{'T; lambda{x. 'a['x]}}
primrw unfold_set_ind : set_ind{'s; x, f, g. 'b['x; 'f; 'g]} <-->
   tree_ind{'s; x, f, g. 'b['x; 'f; 'g]}

interactive_rw reduce_set_ind :
   set_ind{collect{'T; x. 'a['x]}; a, f, g. 'b['a; 'f; 'g]}
   <--> 'b['T; lambda{x. 'a['x]}; lambda{a2. lambda{b2. set_ind{.'a['a2] 'b2; a, f, g. 'b['a; 'f; 'g]}}}]

let fold_pre_set    = makeFoldC << pre_set >> unfold_pre_set
let fold_is_pre_set = makeFoldC << is_pre_set{'t} >> unfold_is_pre_set
let fold_collect    = makeFoldC << collect{'T; x. 'a['x]} >> unfold_collect
let fold_set_ind    = makeFoldC << set_ind{'s; a, f, g. 'b['a; 'f; 'g]} >> unfold_set_ind

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform pre_set_df : pre_set =
   `"pre_set"

dform is_pre_set_df : mode[prl] :: parens :: "prec"[prec_apply] :: is_pre_set{'s} =
   slot{'s} `" pre_set"

dform collect_df : mode[prl] :: parens :: "prec"[prec_apply] :: collect{'T; x. 'a} =
   szone pushm[3] `"collect" " " slot{'x} `":" " " slot{'T} `"." " " slot{'a} popm ezone

dform set_ind_df : mode[prl] :: parens :: "prec"[prec_tree_ind] :: set_ind{'z; a, f, g. 'body} =
   szone pushm[3] `"set_ind(" slot{'g} `"." " "
   pushm[3] `"let tree(" slot{'a} `", " slot{'f} `") =" hspace slot{'z} hspace `"in" popm hspace
   slot{'body} popm ezone

(************************************************************************
 * RELATION TO ITT                                                      *
 ************************************************************************)

(*
 * A set is a type in ITT.
 *)
interactive pre_set_type 'H : :
   sequent ['ext] { 'H >- "type"{pre_set} }

(*
 * Equality from sethood.
 *)
interactive equal_pre_set 'H :
   sequent ['ext] { 'H >- is_pre_set{'s} } -->
   sequent ['ext] { 'H >- 's = 's in pre_set }

(*
 * By assumption.
 *)
interactive is_pre_set_assum 'H 'J : :
   sequent ['ext] { 'H; x: pre_set; 'J['x] >- is_pre_set{'x} }

(*
 * This is how a set is constructed.
 *)
interactive is_pre_set_collect 'H 'y :
   sequent [squash] { 'H >- 'T = 'T in univ[1:l] } -->
   sequent [squash] { 'H; y: 'T >- is_pre_set{'a['y]} } -->
   sequent ['ext] { 'H >- is_pre_set{collect{'T; x. 'a['x]}} }

(*
 * Applications often come up.
 * This is not a necessary interactive, ut it is useful.
 *)
interactive is_pre_set_apply 'H 'J :
   sequent [squash] { 'H; f: 'T -> pre_set; 'J['f] >- 'x = 'x in 'T } -->
   sequent ['ext] { 'H; f: 'T -> pre_set; 'J['f] >- is_pre_set{.'f 'x} }

(*
 * Induction.
 *)
interactive pre_set_elim 'H 'J 'a 'T 'f 'w 'z :
   sequent ['ext] { 'H;
                    a: pre_set;
                    'J['a];
                    T: univ[1:l];
                    f: 'T -> pre_set;
                    w: (all x : 'T. 'C['f 'x]);
                    z: is_pre_set{collect{'T; x. 'f 'x}}
                  >- 'C[collect{'T; x. 'f 'x}]
                  } -->
                     sequent ['ext] { 'H; a: pre_set; 'J['a] >- 'C['a] }

(*
 * Equality on tree induction forms.
 *)
interactive pre_set_ind_equality 'H 'A (bind{x.'B['x]}) 'a 'f 'g :
   sequent [squash] { 'H >- 'z1 = 'z2 in pre_set } -->
   sequent [squash] { 'H; a: 'A; f: 'B['a] -> pre_set; g: a: 'A -> 'B['a] -> 'T >-
      'body1['a; 'f; 'g] = 'body2['a; 'f; 'g] in 'T } -->
   sequent ['ext] { 'H >- set_ind{'z1; a1, f1, g1. 'body1['a1; 'f1; 'g1]}
                          = set_ind{'z2; a2, f2, g2. 'body2['a2; 'f2; 'g2]}
                          in 'T }

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

(*
 * Isset.
 *)
let is_pre_set_term = << is_pre_set{'s} >>
let is_pre_set_opname = opname_of_term is_pre_set_term
let is_is_pre_set_term = is_dep0_term is_pre_set_opname
let mk_is_pre_set_term = mk_dep0_term is_pre_set_opname
let dest_is_pre_set = dest_dep0_term is_pre_set_opname

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let d_collect_is_pre_setT i p =
   if i = 0 then
      let s = maybe_new_vars1 p "s" in
         is_pre_set_collect (hyp_count_addr p) s p
   else
      raise (RefineError ("d_collect_is_pre_setT", StringError "no elimination form"))

(*
 * Special case for collection.
 *)
let is_pre_set_collect_term = << is_pre_set{collect{'T; x. 'a['x]}} >>

let d_resource = d_resource.resource_improve d_resource (is_pre_set_collect_term, d_collect_is_pre_setT)

(*
 * H >- set type
 *)
let d_pre_set_typeT i p =
   if i = 0 then
      pre_set_type (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_pre_set_typeT", StringError "no elimination rule"))

let set_type_term = << "type"{pre_set} >>

let d_resource = d_resource.resource_improve d_resource (set_type_term, d_pre_set_typeT)

(*
 * Set elimination.
 *)
let d_pre_setT i p =
   if i = 0 then
      raise (RefineError ("d_pre_setT", StringError "no introduction rule"))
   else
      let thin =
         if i = hyp_count_addr p then
            thinT i
         else
            idT
      in
      let v_a, h_a = nth_hyp p i in
      let j, k = hyp_indices p i in
      let v_T, v_f, v_b, v_z = maybe_new_vars4 p "T" "f" "b" "z" in
         (pre_set_elim j k v_a v_T v_f v_b v_z thenT thin) p

let pre_set_term = << pre_set >>

let d_resource = d_resource.resource_improve d_resource (pre_set_term, d_pre_setT)

(*
 * Application rule.
 *)
let d_apply_is_pre_setT i p =
   if i = 0 then
      let j = get_sel_arg p in
      let k, l = hyp_indices p j in
         is_pre_set_apply k l p
   else
      raise (RefineError ("d_apply_is_pre_set", StringError "no elimination form"))

let apply_is_pre_set_term = << is_pre_set{.'f 'x} >>

let d_resource = d_resource.resource_improve d_resource (apply_is_pre_set_term, d_apply_is_pre_setT)

(*
 * Typehood of is_pre_set{'s1}
 *)
let d_is_pre_set_typeT i p =
   if i = 0 then
      (rw (addrC [0] unfold_is_pre_set) 0 thenT dT 0) p
   else
      raise (RefineError ("d_is_pre_set_typeT", StringError "no elimination form"))

let is_pre_set_type_term = << "type"{is_pre_set{'s1}} >>

let d_resource = d_resource.resource_improve d_resource (is_pre_set_type_term, d_is_pre_set_typeT)

(*
 * Equal sets.
 *)
let eqPreSetT p =
   equal_pre_set (hyp_count_addr p) p

(*
 * Assumption.
 *)
let preSetAssumT i p =
   let i, j = hyp_indices p i in
      is_pre_set_assum i j p

(*
 * Split a set in a hyp or concl.
 *)
(*
let splitT t i p =
   let v_T, v_f, v_z = maybe_new_vars3 p "T" "f" "z" in
      if i = 0 then
         let goal = var_subst (Sequent.concl p) t v_z in
         let bind = mk_bind_term v_z goal in
            (set_split_concl (hyp_count_addr p) t bind v_T v_f v_z
             thenLT [addHiddenLabelT "wf";
                     addHiddenLabelT "wf";
                     addHiddenLabelT "main"]) p
      else
         let _, hyp = nth_hyp p i in
         let hyp = var_subst hyp t v_z in
         let bind = mk_bind_term v_z hyp in
         let j, k = hyp_indices p i in
            (set_split_hyp2 j k t bind v_T v_f v_z
             thenLT [addHiddenLabelT "wf";
                     addHiddenLabelT "wf";
                     addHiddenLabelT "main"]) p
*)

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

(*
 * Add set assumptions to trivial tactic.
 *)
let trivial_resource =
   trivial_resource.resource_improve trivial_resource (**)
      { auto_name = "preSetAssumT";
        auto_prec = trivial_prec;
        auto_tac = onSomeHypT preSetAssumT
      }

(*
 * A function application.
 *)
let applyT i p =
   let j, k = hyp_indices p i in
      is_pre_set_apply j k p

(*
 * Similar dumb auto tactic.
 *)
let pre_set_autoT =
   firstT [rw fold_is_pre_set 0;
           onSomeHypT applyT]

let pre_set_prec = create_auto_prec [trivial_prec] [back_hyp_prec]

let auto_resource =
   auto_resource.resource_improve auto_resource (**)
      { auto_name = "set_autoT";
        auto_prec = pre_set_prec;
        auto_tac = auto_wrap pre_set_autoT
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
