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

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent
open Var
open Mptop

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
   show_loading "Loading Czf_itt_set%t"

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
 *   collect{'T; x. 'a['x]}:
 *      the set constructed from the family of sets 'a['x]
 *      where 'x ranges over 'T
 *   set_ind is the induction combinator.
 *)
declare set
declare isset{'s}
declare collect{'T; x. 'a['x]}
declare set_ind{'s; x, f, g. 'b['x; 'f; 'g]}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Sets.
 *)
prim_rw unfold_set : set <--> w{univ[1:l]; x. 'x}
prim_rw unfold_isset : isset{'s} <--> ('s = 's in set)
prim_rw unfold_collect : collect{'T; x. 'a['x]} <--> tree{'T; lambda{x. 'a['x]}}
prim_rw unfold_set_ind : set_ind{'s; x, f, g. 'b['x; 'f; 'g]} <-->
   tree_ind{'s; x, f, g. 'b['x; 'f; 'g]}

interactive_rw reduce_set_ind :
   set_ind{collect{'T; x. 'a['x]}; a, f, g. 'b['a; 'f; 'g]}
   <--> 'b['T; lambda{x. 'a['x]}; lambda{a2. lambda{b2. set_ind{.'a['a2] 'b2; a, f, g. 'b['a; 'f; 'g]}}}]

let fold_set        = makeFoldC << set >> unfold_set
let fold_isset      = makeFoldC << isset{'t} >> unfold_isset
let fold_collect    = makeFoldC << collect{'T; x. 'a['x]} >> unfold_collect
let fold_set_ind    = makeFoldC << set_ind{'s; a, f, g. 'b['a; 'f; 'g]} >> unfold_set_ind

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform set_df : set =
   `"set"

dform isset_df : mode[prl] :: parens :: "prec"[prec_apply] :: isset{'s} =
   slot{'s} `" set"

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
interactive set_type {| intro_resource [] |} 'H :
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
interactive isset_assum 'H 'J :
   sequent ['ext] { 'H; x: set; 'J['x] >- isset{'x} }

(*
 * This is how a set is constructed.
 *)
interactive isset_collect {| intro_resource [] |} 'H 'y :
   sequent [squash] { 'H >- 'T = 'T in univ[1:l] } -->
   sequent [squash] { 'H; y: 'T >- isset{'a['y]} } -->
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
interactive set_elim {| elim_resource [ThinOption thinT] |} 'H 'J 'a 'T 'f 'w 'z :
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
interactive set_ind_equality {| intro_resource [] |} 'H 'a 'f 'g 'x :
   ["wf"]   sequent [squash] { 'H >- 'z1 = 'z2 in set } -->
   ["main"] sequent [squash] { 'H; a: univ[1:l]; f: 'a -> set; g: x: univ[1:l] -> 'x -> 'T >-
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

let set_ind_term = << set_ind{'s; T, f, g. 'B['T; 'f; 'g]} >>
let set_ind_opname = opname_of_term set_ind_term
let is_set_ind_term = is_dep0_dep3_term set_ind_opname
let mk_set_ind_term = mk_dep0_dep3_term set_ind_opname
let dest_set_ind = dest_dep0_dep3_term set_ind_opname

(************************************************************************
 * OTHER TACTICS                                                        *
 ************************************************************************)

(*
 * Application rule.
 *)
let d_apply_issetT p =
   let j = get_sel_arg p in
   let k, l = hyp_indices p j in
      isset_apply k l p

let apply_isset_term = << isset{.'f 'x} >>

let intro_resource = Mp_resource.improve intro_resource (apply_isset_term, d_apply_issetT)

(*
 * Typehood of isset{'s1}
 *)
let d_isset_typeT p =
   (rw (addrC [0] unfold_isset) 0 thenT dT 0) p

let isset_type_term = << "type"{isset{'s1}} >>

let intro_resource = Mp_resource.improve intro_resource (isset_type_term, d_isset_typeT)

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
