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

include Czf_itt_eq_inner

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
      eprintf "Loading Czf_itt_set%t" eflush

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
 *   isset{'s}: the judgement that 's is a set
 *   member{'x; 't}:
 *      a. 'x is a set
 *      b. 't is a set
 *      c. 'x is an element of 't
 *)
declare set
declare isset{'s}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Sets.
 *)
prim_rw unfold_set : set <--> (quot x, y: pre_set // eq_inner{'x; 'y})
prim_rw unfold_isset : isset{'s} <--> ('s = 's in set)

let fold_set        = makeFoldC << set >> unfold_set
let fold_isset      = makeFoldC << isset{'t} >> unfold_isset

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform set_df : set =
   `"set"

dform isset_df : mode[prl] :: parens :: "prec"[prec_apply] :: isset{'s} =
   slot{'s} `" set"

(************************************************************************
 * RELATION TO ITT                                                      *
 ************************************************************************)

(*
 * A set is a type in ITT.
 *)
interactive set_type 'H : :
   sequent ['ext] { 'H >- "type"{set} }

(*
 * Equality from sethood.
 *)
interactive equal_set 'H :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- 's = 's in set }

(*
 * By assumption.
 *)
interactive isset_assum 'H 'J : :
   sequent ['ext] { 'H; x: set; 'J['x] >- isset{'x} }

(*
 * Every set is a pre_set.
 *)
interactive is_pre_set_set 'H :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- is_pre_set{'s} }

(*
 * This is how a set is constructed.
 *)
interactive isset_collect2 'H 'y :
   sequent [squash] { 'H >- 'T = 'T in univ[1:l] } -->
   sequent [squash] { 'H; y: 'T >- is_pre_set{'a['y]} } -->
   sequent ['ext] { 'H >- isset{collect{'T; x. 'a['x]}} }

(*
 * Applications often come up.
 * This is not a necessary axiom, ut it is useful.
 *)
interactive isset_apply 'H 'J :
   sequent [squash] { 'H; f: 'T -> set; 'J['f] >- 'x = 'x in 'T } -->
   sequent ['ext] { 'H; f: 'T -> set; 'J['f] >- isset{.'f 'x} }

(*
 * Induction.
 *)
interactive set_elim 'H 'J 'a 'T 'f 'w 'z :
   sequent ['ext] { 'H;
                    a: set;
                    'J['a];
                    T: univ[1:l];
                    f: 'T -> set;
                    w: (all x : 'T. 'C['f 'x]);
                    z: isset{collect{'T; x. 'f 'x}}
                  >- 'C[collect{'T; x. 'f 'x}]
                  } -->
                     sequent ['ext] { 'H; a: set; 'J['a] >- 'C['a] }

(*
 * These are related forms to expand a set into its
 * collect representation.
 *)
interactive set_split_hyp2 'H 'J 's (bind{v. 'A['v]}) 'T 'f 'z :
   sequent [squash] { 'H; x: 'A['s]; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: 'A['s]; 'J['x]; z: set >- "type"{'A['z]} } -->
   sequent ['ext] { 'H;
                    x: 'A['s];
                    'J['x];
                    T: univ[1:l];
                    f: 'T -> set;
                    z: 'A[collect{'T; y. 'f 'y}]
                    >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'A['s]; 'J['x] >- 'C['x] }

interactive set_split_concl 'H 's (bind{v. 'C['v]}) 'T 'f 'z :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; z: set >- "type"{'C['z]} } -->
   sequent ['ext] { 'H; T: univ[1:l]; f: 'T -> set >- 'C[collect{'T; y. 'f 'y}] } -->
   sequent ['ext] { 'H >- 'C['s] }

(*
 * Equality on tree induction forms.
 *)
interactive set_ind_equality 'H 'A (bind{x.'B['x]}) 'a 'f 'g :
   sequent [squash] { 'H >- 'z1 = 'z2 in set } -->
   sequent [squash] { 'H; a: 'A; f: 'B['a] -> set; g: a: 'A -> 'B['a] -> 'T >-
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
let isset_term = << isset{'s} >>
let isset_opname = opname_of_term isset_term
let is_isset_term = is_dep0_term isset_opname
let mk_isset_term = mk_dep0_term isset_opname
let dest_isset = dest_dep0_term isset_opname

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let d_collect_issetT i p =
   if i = 0 then
      let s = maybe_new_vars1 p "s" in
         isset_collect2 (hyp_count_addr p) s p
   else
      raise (RefineError ("d_collect_issetT", StringError "no elimination form"))

(*
 * Special case for collection.
 *)
let isset_collect_term = << isset{collect{'T; x. 'a['x]}} >>

let d_resource = Mp_resource.improve d_resource (isset_collect_term, d_collect_issetT)

(************************************************************************
 * OTHER TACTICS                                                        *
 ************************************************************************)

(*
 * H >- set type
 *)
let d_set_typeT i p =
   if i = 0 then
      set_type (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_set_typeT", StringError "no elimination rule"))

let set_type_term = << "type"{set} >>

let d_resource = Mp_resource.improve d_resource (set_type_term, d_set_typeT)

(*
 * Set elimination.
 *)
let d_setT i p =
   if i = 0 then
      raise (RefineError ("d_setT", StringError "no introduction rule"))
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
         (set_elim j k v_a v_T v_f v_b v_z thenT thin) p

let set_term = << set >>

let d_resource = Mp_resource.improve d_resource (set_term, d_setT)

(*
 * Application rule.
 *)
let d_apply_issetT i p =
   if i = 0 then
      let j = get_sel_arg p in
      let k, l = hyp_indices p j in
         isset_apply k l p
   else
      raise (RefineError ("d_apply_isset", StringError "no elimination form"))

let apply_isset_term = << isset{.'f 'x} >>

let d_resource = Mp_resource.improve d_resource (apply_isset_term, d_apply_issetT)

(*
 * Typehood of isset{'s1}
 *)
let d_isset_typeT i p =
   if i = 0 then
      (rw (addrC [0] unfold_isset) 0 thenT dT 0) p
   else
      raise (RefineError ("d_isset_typeT", StringError "no elimination form"))

let isset_type_term = << "type"{isset{'s1}} >>

let d_resource = Mp_resource.improve d_resource (isset_type_term, d_isset_typeT)

(*
 * Equal sets.
 *)
let eqSetT p =
   equal_set (hyp_count_addr p) p

(*
 * Assumption.
 *)
let setAssumT i p =
   let i, j = hyp_indices p i in
      isset_assum i j p

(*
 * Every set is a pre_set.
 *)
let setPreSetT p =
   is_pre_set_set (hyp_count_addr p) p

(*
 * Split a set in a hyp or concl.
 *)
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

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

(*
 * Add set assumptions to trivial tactic.
 *)
let trivial_resource =
   Mp_resource.improve trivial_resource (**)
      { auto_name = "setAssumT";
        auto_prec = trivial_prec;
        auto_tac = onSomeHypT setAssumT
      }

(*
 * A function application.
 *)
let applyT i p =
   let j, k = hyp_indices p i in
      isset_apply j k p

(*
 * Similar dumb auto tactic.
 *)
let set_autoT =
   firstT [rw fold_isset 0;
           onSomeHypT applyT]

let set_prec = create_auto_prec [trivial_prec] [back_hyp_prec]

let auto_resource =
   Mp_resource.improve auto_resource (**)
      { auto_name = "set_autoT";
        auto_prec = set_prec;
        auto_tac = auto_wrap set_autoT
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
