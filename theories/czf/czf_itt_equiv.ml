include Czf_itt_set
include Czf_itt_member
include Czf_itt_pair

open Itt_equal

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Sequent
open Tactic_type.Tacticals
open Var
open Mptop

open Base_dtactic
open Base_auto_tactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare equiv{'s; 'r; 'a; 'b}
declare equiv{'s; 'r}

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let equiv_term = << equiv{'s; 'r; 'a; 'b} >>
let equiv_opname = opname_of_term equiv_term
let is_equiv_term = is_dep0_dep0_dep0_dep0_term equiv_opname
let dest_equiv = dest_dep0_dep0_dep0_dep0_term equiv_opname
let mk_equiv_term = mk_dep0_dep0_dep0_dep0_term equiv_opname

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_equiv : equiv{'s; 'r; 'a; 'b} <-->
   (((isset{'s} & isset{'r} & isset{'a} & isset{'b}) & mem{'a; 's} & mem{'b; 's}) & mem{pair{'a; 'b}; 'r})

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform equiv_df1 : parens :: except_mode[src] :: equiv{'s; 'r} =
   `"equiv(" slot{'s} `"; " slot{'r} `")"

dform equiv_df2 : parens :: except_mode[src] :: equiv{'s; 'r; 'a; 'b} =
   `"equiv(" slot{'s} `"; " slot{'r} `"; " slot{'a} `"; " slot{'b} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive equiv_rel_type {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'r} } -->
   sequent ['ext] { 'H >- "type"{equiv{'s; 'r}} }

interactive equiv_type {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'r} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent ['ext] { 'H >- "type"{equiv{'s; 'r; 'a; 'b}} }

interactive equiv_intro {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   [wf] sequent [squash] { 'H >- isset{'a} } -->
   [wf] sequent [squash] { 'H >- isset{'b} } -->
   sequent ['ext] { 'H >- mem{'a; 's} } -->
   sequent ['ext] { 'H >- mem{'b; 's} } -->
   sequent ['ext] { 'H >- mem{pair{'a; 'b}; 'r} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r; 'a; 'b} }

(*
 * An equivalence relation on a set S is a relation
 * on S satisfying reflexivity, symmetry, and transitivity.
 *)
interactive equiv_ref_intro {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   [wf] sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; 's} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r; 'a; 'a} }

interactive equiv_rel_intro {| intro [] |} 'H 'b 'c 'd 'e 'f :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
(*   sequent ['ext] { 'H >- equiv{'s; 'r; 'a; 'a} } --> *)
   sequent ['ext] { 'H; u: equiv{'s; 'r; 'b; 'c} >- equiv{'s; 'r; 'c; 'b} } -->
   sequent ['ext] { 'H; u: equiv{'s; 'r; 'd; 'e}; v: equiv{'s; 'r; 'e; 'f} >- equiv{'s; 'r; 'd; 'f}} -->
   sequent ['ext] { 'H >- equiv{'s; 'r} }

interactive equiv_sym 'H 'J 'u :
   sequent [squash] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- isset{'r} } -->
   sequent [squash] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- isset{'a} } -->
   sequent [squash] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- isset{'b} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- mem{'a; 's} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- mem{'b; 's} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x]; u: equiv{'s; 'r; 'b; 'a} >- 'C['x] } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- 'C['x] }

interactive equiv_trans 'H 'J 'c 'u 'v :
   sequent [squash] { 'H; x: equiv{'s; 'r}; y: equiv{'s; 'r; 'a; 'b}; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- isset{'r} } -->
   sequent [squash] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- isset{'a} } -->
   sequent [squash] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- isset{'c} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- mem{'a; 's} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- mem{'b; 's} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- mem{'c; 's} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x]; u: equiv{'s; 'r; 'a; 'c}; v: equiv{'s; 'r; 'c; 'b} >- 'C['x] } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- 'C['x] }

let equivSymT i p =
   let u = maybe_new_vars1 p "u" in
   let j, k = Sequent.hyp_indices p i in
      equiv_sym j k u p

let equivTransT t i p =
   let u, v = maybe_new_vars2 p "u" "v" in
   let j, k = Sequent.hyp_indices p i in
      equiv_trans j k t u v p

interactive equiv_fun {| intro [] |} 'H :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f3['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f4['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. equiv{'f1['z]; 'f2['z]; 'f3['z]; 'f4['z]}} }

interactive equiv_rel_fun {| intro [] |} 'H :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. equiv{'f1['z]; 'f2['z]}} }

interactive equiv_hyp_subst 'H 'J 's 'r 's1 's2 (bind{v. 'P['v]}) 'z :
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- equiv{'s; 'r; 's1; 's2} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x]; z: 'P['s2] >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- fun_prop{z. 'P['z]} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- 'C['x] }

interactive equiv_concl_subst 'H 's 'r 's1 's2 (bind{v. 'C['v]}) 'z :
   sequent ['ext] { 'H >- equiv{'s; 'r; 's1; 's2} } -->
   sequent ['ext] { 'H >- 'C['s2] } -->
   sequent ['ext] { 'H >- fun_prop{z. 'C['z]} } -->
   sequent ['ext] { 'H >- 'C['s1] }

let equivConclSubstT t p =
   let s, r, s1, s2 = dest_equiv t in
   let goal = Sequent.concl p in
   let z = maybe_new_vars1 p "v" in
   let bind = mk_xbind_term z (var_subst goal s1 z) in
      (equiv_concl_subst (hyp_count_addr p) s r s1 s2 bind z
       thenLT [addHiddenLabelT "eq";
               addHiddenLabelT "main";
               addHiddenLabelT "wf"]) p

let equivHypSubstT t i p =
   let s, r, s1, s2 = dest_equiv t in
   let _, hyp = nth_hyp p i in
   let z = maybe_new_vars1 p "v" in
   let bind = mk_xbind_term z (var_subst hyp s1 z) in
   let j, k = hyp_indices p i in
      (equiv_hyp_subst j k s r s1 s2 bind z
       thenLT [addHiddenLabelT "eq";
               addHiddenLabelT "main";
               addHiddenLabelT "wf"]) p

let equivSubstT t i =
   if i = 0 then
      equivConclSubstT t
   else
      equivHypSubstT t i
