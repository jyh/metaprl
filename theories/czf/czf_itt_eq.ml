(*
 * We define an equality on sets.
 * The normal intensional equality ('s1 = 's2 in set) is
 * not sufficient, because it is not a small type (it is in U2).
 *
 * We define and extensional equality by induction
 * on the sets.
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
 *)

include Czf_itt_set

open Itt_equal

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Nl_resource

open Sequent
open Tacticals
open Var
open Nltop

open Base_auto_tactic

open Itt_equal
open Itt_rfun
open Itt_struct

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare eq{'s1; 's2}
declare eq_inner{'s1; 's2}
declare fun_set{z. 'f['z]}
declare fun_prop{z. 'P['z]}
declare dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw reduce_eq_inner : eq_inner{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((all y1 : 'T1. exst y2: 'T2. eq_inner{.'f1['y1]; .'f2['y2]})
    & (all y2 : 'T2. exst y1: 'T1. eq_inner{.'f1['y1]; .'f2['y2]}))

primrw unfold_eq : eq{'s1; 's2} <-->
   ((isset{'s1} & isset{'s2}) & eq_inner{'s1; 's2})

interactive_rw reduce_eq : eq{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((isset{collect{'T1; x1. 'f1['x1]}} & isset{collect{'T2; x2. 'f2['x2]}})
   & ((all y1 : 'T1. exst y2: 'T2. eq_inner{.'f1['y1]; .'f2['y2]})
     & (all y2 : 'T2. exst y1: 'T1. eq_inner{.'f1['y1]; .'f2['y2]})))

(*
 * A functional predicate can produce proofs for
 * all equal sets.
 *)
primrw unfold_fun_set : fun_set{z. 'f['z]} <-->
    (all s1: set. all s2: set. (eq{'s1; 's2} => eq{'f['s1]; 'f['s2]}))

primrw unfold_fun_prop : fun_prop{z. 'P['z]} <-->
    (all s1: set. all s2: set. (eq{'s1; 's2} => 'P['s1] => 'P['s2]))

(*
 * This is _pointwise_ functionality.
 *)
primrw unfold_dfun_prop : dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]} <-->
  (all s1: set. all s2: set. (eq{'s1; 's2} => (u1: 'A['s1] -> 'B['s1; 'u1] -> u2: 'A['s2] -> 'B['s2; 'u2])))

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform eq_df : mode[prl] :: parens :: "prec"[prec_equal] :: eq{'s1; 's2} =
   slot{'s1} `" =' " slot{'s2}

dform eq_inner_df : mode[prl] :: eq_inner{'s1; 's2} =
   `"eq_inner(" slot {'s1} `"; " slot{'s2} `")"

dform fun_set_df : mode[prl] :: parens :: "prec"[prec_apply] :: fun_set{x. 'P} =
   Nuprl_font!forall slot{'x} `"." slot{'P} `" fun_set"

dform fun_set_df : mode[prl] :: parens :: "prec"[prec_apply] :: fun_prop{x. 'P} =
   Nuprl_font!forall slot{'x} `"." slot{'P} `" fun_prop"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Membership in a universe.
 *)
interactive eq_inner_equality1 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} = eq_inner{'s1; 's2} in univ[1:l] }

(*
 * Membership in a universe.
 *)
interactive eq_inner_type 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- "type"{eq_inner{'s1; 's2}} }

(*
 * More general equality in a universe.
 *)
interactive eq_inner_equality2 'H :
   sequent [squash] { 'H >- 's1 = 's3 in set } -->
   sequent [squash] { 'H >- 's2 = 's4 in set } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} = eq_inner{'s3; 's4} in univ[1:l] }

(*
 * Equality typehood.
 *)
interactive eq_type 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- "type"{eq{'s1; 's2}} }

(*
 * Equality is over sets.
 *)
interactive eq_isset_left 'H 's2 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- isset{'s1} }

interactive eq_isset_right 'H 's1 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- isset{'s2} }

(*
 * Reflexivity.
 *)
interactive eq_ref 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- eq{'s1; 's1} }

(*
 * Symettry.
 *)
interactive eq_sym 'H :
   sequent ['ext] { 'H >- eq{'s2; 's1} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} }

(*
 * Transitivity.
 *)
interactive eq_trans 'H 's2 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- eq{'s2; 's3} } -->
   sequent ['ext] { 'H >- eq{'s1; 's3} }

(*
 * Finally, functionality puts them all together.
 *)
interactive eq_fun 'H :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. eq{'f1['z]; 'f2['z]}} }

interactive eq_inner_fun 'H :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. eq_inner{'f1['z]; 'f2['z]}} }

(*
 * Substitution over functional expressions.
 *)
interactive eq_hyp_subst 'H 'J 's1 's2 (bind{v. 'P['v]}) 'z :
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x]; z: 'P['s2] >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- fun_prop{z. 'P['z]} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- 'C['x] }

interactive eq_concl_subst 'H 's1 's2 (bind{v. 'C['v]}) 'z :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- 'C['s2] } -->
   sequent ['ext] { 'H >- fun_prop{z. 'C['z]} } -->
   sequent ['ext] { 'H >- 'C['s1] }

(*
 * Typehood of functionality.
 *)
interactive fun_set_type 'H :
   sequent ['ext] { 'H; z: set >- isset{'f['z]} } -->
   sequent ['ext] { 'H >- "type"{fun_set{z. 'f['z]}} }

interactive fun_prop_type 'H :
   sequent [squash] { 'H; z: set >- "type"{'f['z]} } -->
   sequent ['ext] { 'H >- "type"{fun_prop{z. 'f['z]}} }

(*
 * Unquantified sets are functional.
 *)
interactive fun_set 'H :
   sequent ['ext] { 'H >- isset{'u} } -->
   sequent ['ext] { 'H >- fun_set{z. 'u} }

interactive fun_ref 'H : :
   sequent ['ext] { 'H >- fun_set{z. 'z} }

interactive fun_prop 'H :
   sequent [squash] { 'H >- "type"{'P} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'P} }

(*
 * LEMMAS:
 * Every functional type is a type.
 *)
interactive fun_set_is_set 'H (bind{z. 'P['z]}) 's :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- fun_set{z. 'P['z]} } -->
   sequent ['ext] { 'H >- isset{'P['s]} }

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let eq_term = << eq{'s1; 's2} >>
let eq_opname = opname_of_term eq_term
let is_eq_term = is_dep0_dep0_term eq_opname
let dest_eq = dest_dep0_dep0_term eq_opname
let mk_eq_term = mk_dep0_dep0_term eq_opname

let fun_set_term = << fun_set{z. 's['z]} >>
let fun_set_opname = opname_of_term fun_set_term
let is_fun_set_term = is_dep1_term fun_set_opname
let dest_fun_set = dest_dep1_term fun_set_opname
let mk_fun_set_term = mk_dep1_term fun_set_opname

let fun_prop_term = << fun_prop{z. 's['z]} >>
let fun_prop_opname = opname_of_term fun_prop_term
let is_fun_prop_term = is_dep1_term fun_prop_opname
let dest_fun_prop = dest_dep1_term fun_prop_opname
let mk_fun_prop_term = mk_dep1_term fun_prop_opname

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Functionality.
 *)
let d_fun_set_typeT i p =
   if i = 0 then
      fun_set_type (hyp_count_addr p) p
   else
      raise (RefineError ("d_fun_set_typeT", StringError "no elimination form"))

let fun_set_type_term = << "type"{fun_set{z. 'f['z]}} >>

let d_resource = d_resource.resource_improve d_resource (fun_set_type_term, d_fun_set_typeT)

let d_fun_prop_typeT i p =
   if i = 0 then
      fun_prop_type (hyp_count_addr p) p
   else
      raise (RefineError ("d_fun_prop_typeT", StringError "no elimination form"))

let fun_prop_type_term = << "type"{fun_prop{z. 'f['z]}} >>

let d_resource = d_resource.resource_improve d_resource (fun_prop_type_term, d_fun_prop_typeT)

(*
 * Equality of inner equality.
 *)
let eqcd_eq_innerT p =
   let goal = Sequent.concl p in
   let _, eq1, eq2 = dest_equal goal in
   let j = hyp_count_addr p in
      if alpha_equal eq1 eq2 then
         eq_inner_equality1 j p
      else
         eq_inner_equality2 j p

let eq_inner_term = << eq_inner{'s1; 's2} >>

let eq_inner_equal_term = << eq_inner{'s1; 's2} = eq_inner{'s3; 's4} in univ[1:l] >>

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (eq_inner_term, eqcd_eq_innerT)

let d_resource = d_resource.resource_improve d_resource (eq_inner_equal_term, d_wrap_eqcd eqcd_eq_innerT)

(*
 * Typehood.
 *)
let d_eq_inner_typeT i p =
   if i = 0 then
      eq_inner_type (hyp_count_addr p) p
   else
      raise (RefineError ("d_eq_inner_typeT", StringError "no elimination form"))

let eq_inner_type_term = << "type"{eq_inner{'s1; 's2}} >>

let d_resource = d_resource.resource_improve d_resource (eq_inner_type_term, d_eq_inner_typeT)

(*
 * Functionality.
 *)
let d_eq_inner_funT i p =
   if i = 0 then
      eq_inner_fun (hyp_count_addr p) p
   else
      raise (RefineError ("d_eq_inner_funT", StringError "no elimination form"))

let eq_inner_fun_term = << fun_prop{z. eq_inner{'s1['z]; 's2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (eq_inner_fun_term, d_eq_inner_funT)

(*
 * Equality typehood.
 *)
let d_eq_typeT i p =
   if i = 0 then
      eq_type (hyp_count_addr p) p
   else
      raise (RefineError ("d_eq_typeT", StringError "no elimination form"))

let eq_type_term = << "type"{eq{'s1; 's2}} >>

let d_resource = d_resource.resource_improve d_resource (eq_type_term, d_eq_typeT)

(*
 * Functionality.
 *)
let d_eq_funT i p =
   if i = 0 then
      eq_fun (hyp_count_addr p) p
   else
      raise (RefineError ("d_eq_funT", StringError "no elimination form"))

let eq_fun_term = << fun_prop{z. eq{'s1['z]; 's2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (eq_fun_term, d_eq_funT)

(*
 * Unquantified sets.
 * This tactic only works on the forms:
 *    fun_set{z. v}
 *)
let d_fun_setT i p =
   if i = 0 then
      let concl = Sequent.concl p in
      let v, t = dest_fun_set concl in
      let tac =
         if is_var_term t then
            let v' = dest_var t in
               if v' = v then
                  fun_ref
               else
                  fun_set
         else if is_free_var v t then
            raise (RefineError ("d_fun_setT", StringStringError ("variable is free", v)))
         else
            fun_set
      in
         tac (hyp_count_addr p) p
   else
      raise (RefineError ("d_fun_setT", StringError "no elimination form"))

let fun_set_term = << fun_set{z. 'u} >>

let d_resource = d_resource.resource_improve d_resource (fun_set_term, d_fun_setT)

let d_fun_propT i p =
   if i = 0 then
      let concl = Sequent.concl p in
      let v, t = dest_fun_prop concl in
         if is_free_var v t then
            raise (RefineError ("d_fun_propT", StringStringError ("variable is free", v)))
         else
            fun_prop (hyp_count_addr p) p
   else
      raise (RefineError ("d_fun_propT", StringError "no elimination form"))

let fun_prop_term = << fun_prop{z. 'P} >>

let d_resource = d_resource.resource_improve d_resource (fun_prop_term, d_fun_propT)

(*
 * Substitution.
 *)
let setConclSubstT t p =
   let s1, s2 = dest_eq t in
   let goal = Sequent.concl p in
   let z = maybe_new_vars1 p "v" in
   let bind = mk_bind_term z (var_subst goal s1 z) in
      (eq_concl_subst (hyp_count_addr p) s1 s2 bind z
       thenLT [addHiddenLabelT "eq";
               addHiddenLabelT "main";
               addHiddenLabelT "wf"]) p

let setHypSubstT t i p =
   let s1, s2 = dest_eq t in
   let _, hyp = nth_hyp p i in
   let z = maybe_new_vars1 p "v" in
   let bind = mk_bind_term z (var_subst hyp s1 z) in
   let j, k = hyp_indices p i in
      (eq_hyp_subst j k s1 s2 bind z
       thenLT [addHiddenLabelT "eq";
               addHiddenLabelT "main";
               addHiddenLabelT "wf"]) p

let setSubstT t i =
   if i = 0 then
      setConclSubstT t
   else
      setHypSubstT t i

(*
 * Equality relations.
 *)
let eqSetRefT p =
   eq_ref (hyp_count_addr p) p

let eqSetSymT p =
   eq_sym (hyp_count_addr p) p

let eqSetTransT t p =
   eq_trans (hyp_count_addr p) t p

(*
 * Sethood.
 *)
let eqSetLeftT t p =
   eq_isset_left (hyp_count_addr p) t p

let eqSetRightT t p =
   eq_isset_right (hyp_count_addr p) t p

(*
 * Always reasonable to try reflexivity.
 *)
let auto_resource =
   auto_resource.resource_improve auto_resource (**)
      { auto_name = "eqSetRefT";
        auto_prec = trivial_prec;
        auto_tac = auto_wrap eqSetRefT
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
