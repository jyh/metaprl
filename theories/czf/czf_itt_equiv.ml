include Czf_itt_set
include Czf_itt_member
include Czf_itt_pair
include Czf_itt_set_bvd

open Printf
open Mp_debug
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

open Itt_rfun
open Czf_itt_set

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare equiv{'s; 'r; 'a; 'b}
declare equiv{'s; 'r}
declare equiv_fun_set{'s; 'r; z. 'f['z]}
declare equiv_fun_prop{'s; 'r; z. 'P['z]}
(*declare equiv_dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]}*)

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let equiv_term = << equiv{'s; 'r; 'a; 'b} >>
let equiv_opname = opname_of_term equiv_term
let is_equiv_term = is_dep0_dep0_dep0_dep0_term equiv_opname
let dest_equiv = dest_dep0_dep0_dep0_dep0_term equiv_opname
let mk_equiv_term = mk_dep0_dep0_dep0_dep0_term equiv_opname

let equiv_fun_set_term = << equiv_fun_set{'s; 'r; z. 's['z]} >>
let equiv_fun_set_opname = opname_of_term equiv_fun_set_term
let is_equiv_fun_set_term = is_dep0_dep0_dep1_term equiv_fun_set_opname
let dest_equiv_fun_set = dest_dep0_dep0_dep1_term equiv_fun_set_opname
let mk_equiv_fun_set_term = mk_dep0_dep0_dep1_term equiv_fun_set_opname

let equiv_fun_prop_term = << equiv_fun_prop{'s; 'r; z. 's['z]} >>
let equiv_fun_prop_opname = opname_of_term equiv_fun_prop_term
let is_equiv_fun_prop_term = is_dep0_dep0_dep1_term equiv_fun_prop_opname
let dest_equiv_fun_prop = dest_dep0_dep0_dep1_term equiv_fun_prop_opname
let mk_equiv_fun_prop_term = mk_dep0_dep0_dep1_term equiv_fun_prop_opname

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_equiv : equiv{'s; 'r; 'a; 'b} <-->
   (((isset{'s} & isset{'r} & isset{'a} & isset{'b}) & mem{'a; 's} & mem{'b; 's}) & mem{pair{'a; 'b}; 'r})

prim_rw unfold_equiv_fun_set : equiv_fun_set{'s; 'r; z. 'f['z]} <-->
   (all a: set. all b: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b} => equiv{'s; 'r; 'f['a]; 'f['b]}))

prim_rw unfold_equiv_fun_prop : equiv_fun_prop{'s; 'r; z. 'P['z]} <-->
    (all a: set. all b: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b} => 'P['a] => 'P['b]))

(*prim_rw unfold_equiv_dfun_prop : equiv_dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]} <-->
   (all s: set. all r: set. all a: set. all b: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b} => (u1: 'A['a] -> 'B['a; 'u1] -> u2: 'A['b] -> 'B['b; 'u2])))
*)

let fold_equiv = makeFoldC << equiv{'s; 'r; 'a; 'b} >> unfold_equiv

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform equiv_df1 : parens :: except_mode[src] :: equiv{'s; 'r} =
   `"equiv(" slot{'s} `"; " slot{'r} `")"

dform equiv_df2 : parens :: except_mode[src] :: equiv{'s; 'r; 'a; 'b} =
   `"equiv(" slot{'s} `"; " slot{'r} `"; " slot{'a} `"; " slot{'b} `")"

dform equiv_fun_set_df : except_mode[src] :: parens :: "prec"[prec_apply] :: equiv_fun_set{'s; 'r; x. 'P} =
   Nuprl_font!forall slot{'x} `"." slot{'P} `" equiv_fun_set"

dform equiv_fun_prop_df : except_mode[src] :: parens :: "prec"[prec_apply] :: equiv_fun_prop{'s; 'r; z. 'P} =
   Nuprl_font!forall slot{'z} `"." slot{'P} `" equiv_fun_prop"

(*dform equiv_dfun_prop_df : except_mode[src] :: parens :: "prec"[prec_apply] :: equiv_dfun_prop{u. 'A; x, y. 'P} =
   szone pushm[0]
   Nuprl_font!forall slot{'u} `":" slot{'A} `"." hspace slot{'x} `"," slot{'y} `"." slot{'P} `" equiv_dfun_prop"
   popm ezone
*)
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

interactive equiv_rel_intro {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
(* sequent ['ext] { 'H >- equiv{'s; 'r; 'a; 'a} } --> *)
   sequent ['ext] { 'H; b: set; c: set; x: mem{'b; 's}; y: mem{'c; 's}; u: equiv{'s; 'r; 'b; 'c} >- equiv{'s; 'r; 'c; 'b} } -->
   sequent ['ext] { 'H; d: set; e: set; f: set; x: mem{'d; 's}; y: mem{'e; 's}; z: mem{'f; 's}; u: equiv{'s; 'r; 'd; 'e}; v: equiv{'s; 'r; 'e; 'f} >- equiv{'s; 'r; 'd; 'f}} -->
   sequent ['ext] { 'H >- equiv{'s; 'r} }

interactive equiv_sym 'H  :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'r} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- mem{'a; 's} } -->
   sequent ['ext] { 'H >- mem{'b; 's} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r; 'a; 'b} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r; 'b; 'a} }

interactive equiv_trans 'H 'b :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'r} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'c} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- mem{'a; 's} } -->
   sequent ['ext] { 'H >- mem{'b; 's} } -->
   sequent ['ext] { 'H >- mem{'c; 's} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r; 'a; 'b} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r; 'b; 'c} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r; 'a; 'c} }

let equivRefT p =
   equiv_ref_intro (hyp_count_addr p) p

let equivSymT p =
   equiv_sym (hyp_count_addr p) p

let equivTransT t p =
   equiv_trans (hyp_count_addr p) t p

interactive equiv_sym1 'H 'J 'u :
   sequent [squash] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- isset{'r} } -->
   sequent [squash] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- isset{'a} } -->
   sequent [squash] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- isset{'b} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- mem{'a; 's} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- mem{'b; 's} } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x]; u: equiv{'s; 'r; 'b; 'a} >- 'C['x] } -->
   sequent ['ext] { 'H; x: equiv{'s; 'r; 'a; 'b}; 'J['x] >- 'C['x] }

let equivSym1T i p =
   let u = maybe_new_vars1 p "u" in
   let j, k = Sequent.hyp_indices p i in
      equiv_sym1 j k u p

interactive equiv_fun_isset 'H 'J equiv_fun_set{'s; 'r; z. 'f['z]} :
   sequent [squash] { 'H; z: set; 'J['z] >- isset{'s} } -->
   sequent [squash] { 'H; z: set; 'J['z] >- isset{'r} } -->
   sequent ['ext] { 'H; z: set; 'J['z] >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H; z: set; 'J['z] >- mem{'z; 's} } -->
   sequent ['ext] { 'H; z: set; 'J['z] >- equiv_fun_set{'s; 'r; z. 'f['z]} } -->
   sequent ['ext] { 'H; z: set; 'J['z] >- isset{'f['z]} }

interactive equiv_fun_mem 'H 'J equiv_fun_set{'s; 'r; z. 'f['z]} :
   sequent [squash] { 'H; z: set; 'J['z] >- isset{'s} } -->
   sequent [squash] { 'H; z: set; 'J['z] >- isset{'r} } -->
   sequent ['ext] { 'H; z: set; 'J['z] >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H; z: set; 'J['z] >- mem{'z; 's} } -->
   sequent ['ext] { 'H; z: set; 'J['z] >- equiv_fun_set{'s; 'r; z. 'f['z]} } -->
   sequent ['ext] { 'H; z: set; 'J['z] >- mem{'f['z]; 's} }

let equivFunSetT i p =
   let z, _ = Sequent.nth_hyp p i in
   let t = dest_isset (Sequent.concl p) in
   let t =
      try
         let l = Sequent.get_term_list_arg p "with" in
            match l with
               [s; r] -> mk_equiv_fun_set_term s r z t
             | _ -> raise(RefineError ("equivFunSetT", StringError ("wrong number of terms")))
      with RefineError ("get_attribute",_) ->
         raise (RefineError ("equivFunSetT", StringError ("need a term list")))
   in
      let j, k = Sequent.hyp_indices p i in
         equiv_fun_isset j k t p

let equivFunMemT t i p =
   let z, _ = Sequent.nth_hyp p i in
   let t =
      try
         let l = Sequent.get_term_list_arg p "with" in
            match l with
               [s; r] -> mk_equiv_fun_set_term s r z t
             | _ -> raise(RefineError ("equivFunSetT", StringError ("wrong number of terms")))
      with RefineError ("get_attribute",_) ->
         raise (RefineError ("equivFunSetT", StringError ("need a term list")))
   in
      let j, k = Sequent.hyp_indices p i in
         equiv_fun_mem j k t p

interactive equiv_id_fun {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- equiv_fun_set{'s; 'r; z. 'z} }

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

interactive equiv_set_fun1 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'a} } -->
   [wf] sequent [squash] { 'H >- isset{'b} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. equiv{'f1['z]; 'f2['z]; 'a; 'b}} }

interactive equiv_elem_fun1 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. equiv{'s; 'r; 'f1['z]; 'f2['z]}} }

interactive equiv_elem_fun2 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   [wf] sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- mem{'a; 's} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. equiv{'s; 'r; 'a; 'f1['z]}} }

interactive equiv_elem_fun3 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   [wf] sequent [squash] { 'H >- isset{'b} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- mem{'b; 's} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. equiv{'s; 'r; 'f1['z]; 'b}} }

interactive equiv_elem_fun4 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   [wf] sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- mem{'a; 's} } -->
   sequent ['ext] { 'H >- fun_prop{z. equiv{'s; 'r; 'a; 'z}} }

interactive equiv_elem_fun5 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   [wf] sequent [squash] { 'H >- isset{'b} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- mem{'b; 's} } -->
   sequent ['ext] { 'H >- fun_prop{z. equiv{'s; 'r; 'z; 'b}} }

interactive equiv_elem_equiv_fun1 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- equiv_fun_set{'s; 'r; z. 'f1['z]} } -->
   sequent ['ext] { 'H >- equiv_fun_set{'s; 'r; z. 'f2['z]} } -->
   sequent ['ext] { 'H >- equiv_fun_prop{'s; 'r; z. equiv{'s; 'r; 'f1['z]; 'f2['z]}} }

interactive equiv_elem_equiv_fun2 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   [wf] sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; 's} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- equiv_fun_set{'s; 'r; z. 'f1['z]} } -->
   sequent ['ext] { 'H >- equiv_fun_prop{'s; 'r; z. equiv{'s; 'r; 'a; 'f1['z]}} }

interactive equiv_elem_equiv_fun3 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   [wf] sequent [squash] { 'H >- isset{'b} } -->
   sequent ['ext] { 'H >- mem{'b; 's} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- equiv_fun_set{'s; 'r; z. 'f1['z]} } -->
   sequent ['ext] { 'H >- equiv_fun_prop{'s; 'r; z. equiv{'s; 'r; 'f1['z]; 'b}} }

interactive equiv_elem_equiv_fun4 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   [wf] sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; 's} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- equiv_fun_prop{'s; 'r; z. equiv{'s; 'r; 'a; 'z}} }

interactive equiv_elem_equiv_fun5 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   [wf] sequent [squash] { 'H >- isset{'b} } -->
   sequent ['ext] { 'H >- mem{'b; 's} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- equiv_fun_prop{'s; 'r; z. equiv{'s; 'r; 'z; 'b}} }

interactive equiv_hyp_subst 'H 'J 's 'r 's1 's2 (bind{w. 'P['w]}) 'z :
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- equiv{'s; 'r; 's1; 's2} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x]; z: 'P['s2] >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- equiv_fun_prop{'s; 'r; z. 'P['z]} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- 'C['x] }

interactive equiv_concl_subst 'H 's 'r 's1 's2 (bind{w. 'C['w]}) :
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r; 's1; 's2} } -->
   sequent ['ext] { 'H >- 'C['s2] } -->
   sequent ['ext] { 'H >- equiv_fun_prop{'s; 'r; z. 'C['z]} } -->
   sequent ['ext] { 'H >- 'C['s1] }

let equivConclSubstT t p =
   let s, r, s1, s2 = dest_equiv t in
   let goal = Sequent.concl p in
   let bind =
      try
         let t1 = get_with_arg p in
            if is_xbind_term t1 then
               t1
            else
               raise generic_refiner_exn (* will be immedeiatelly caugh *)
      with
         RefineError _ ->
            let w = maybe_new_vars1 p "w" in
                mk_xbind_term w (var_subst goal s1 w)
   in
      equiv_concl_subst (hyp_count_addr p) s r s1 s2 bind p

let equivHypSubstT t i p =
   let s, r, s1, s2 = dest_equiv t in
   let j, k = hyp_indices p i in
   let _, hyp = nth_hyp p i in
   let z = maybe_new_vars1 p "z" in
   let bind =
      try
         let t1 = get_with_arg p in
            if is_xbind_term t1 then
               t1
            else
               raise generic_refiner_exn (* will be immedeiatelly caugh *)
      with
         RefineError _ ->
            let w = maybe_new_vars1 p "w" in
                mk_xbind_term w (var_subst hyp s1 w)
   in
      equiv_hyp_subst j k s r s1 s2 bind z p

let equivSubstT t i =
   if i = 0 then
      equivConclSubstT t
   else
      equivHypSubstT t i

(*
 * Always reasonable to try reflexivity.
 *)
let resource auto += [{
   auto_name = "equivRefT";
   auto_prec = trivial_prec;
   auto_tac = equivRefT;
   auto_type = AutoNormal;
}]

interactive equiv_fun_set_type {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent [squash] { 'H; z: set >- isset{'f['z]} } -->
   sequent ['ext] { 'H >- "type"{equiv_fun_set{'s; 'r; z. 'f['z]}} }

interactive equiv_fun_prop_type {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent [squash] { 'H; z: set >- "type"{'f['z]} } -->
   sequent ['ext] { 'H >- "type"{equiv_fun_prop{'s; 'r; z. 'f['z]}} }

(* The trivial cases. *)
interactive equiv_fun_set {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent [squash] { 'H >- isset{'u} } -->
   sequent ['ext] { 'H >- mem{'u; 's} } -->
   sequent ['ext] { 'H >- equiv_fun_set{'s; 'r; z. 'u} }

interactive equiv_fun_ref {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H >- equiv_fun_set{'s; 'r; z. 'z} }

interactive equiv_fun_prop {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s} } -->
   [wf] sequent [squash] { 'H >- isset{'r} } -->
   sequent ['ext] { 'H >- equiv{'s; 'r} } -->
   sequent [squash] { 'H >- "type"{'P} } -->
   sequent ['ext] { 'H >- equiv_fun_prop{'s; 'r; z. 'P} }

interactive eq_equiv_elim {| elim [] |} 'H 'J 's 'r :
   sequent [squash] { 'H; x: eq{'a; 'b}; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: eq{'a; 'b}; 'J['x] >- isset{'r} } -->
   sequent [squash] { 'H; x: eq{'a; 'b}; 'J['x] >- isset{'a} } -->
   sequent [squash] { 'H; x: eq{'a; 'b}; 'J['x] >- isset{'b} } -->
   sequent ['ext] { 'H; x: eq{'a; 'b}; 'J['x] >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H; x: eq{'a; 'b}; 'J['x] >- mem{'a; 's} } -->
   sequent ['ext] { 'H; x: eq{'a; 'b}; 'J['x] >- mem{'b; 's} } -->
   sequent ['ext] { 'H; x: eq{'a; 'b}; 'J['x]; y: equiv{'s; 'r; 'a; 'b} >- 'C['x] } -->
   sequent ['ext] { 'H; x: eq{'a; 'b}; 'J['x] >- 'C['x] }

interactive equal_equiv_elim {| elim [] |} 'H 'J 's 'r :
   sequent [squash] { 'H; x: equal{'a; 'b}; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: equal{'a; 'b}; 'J['x] >- isset{'r} } -->
   sequent [squash] { 'H; x: equal{'a; 'b}; 'J['x] >- isset{'a} } -->
   sequent [squash] { 'H; x: equal{'a; 'b}; 'J['x] >- isset{'b} } -->
   sequent ['ext] { 'H; x: equal{'a; 'b}; 'J['x] >- equiv{'s; 'r} } -->
   sequent ['ext] { 'H; x: equal{'a; 'b}; 'J['x] >- mem{'a; 's} } -->
   sequent ['ext] { 'H; x: equal{'a; 'b}; 'J['x] >- mem{'b; 's} } -->
   sequent ['ext] { 'H; x: equal{'a; 'b}; 'J['x]; y: equiv{'s; 'r; 'a; 'b} >- 'C['x] } -->
   sequent ['ext] { 'H; x: equal{'a; 'b}; 'J['x] >- 'C['x] }

interactive pair_eq {| elim [] |} 'H 'J :
   sequent [squash] { 'H; x: eq{pair{'a; 'b}; pair{'z; 'z}}; 'J['x] >- isset{'z} } -->
   sequent [squash] { 'H; x: eq{pair{'a; 'b}; pair{'z; 'z}}; 'J['x] >- isset{'a} } -->
   sequent [squash] { 'H; x: eq{pair{'a; 'b}; pair{'z; 'z}}; 'J['x] >- isset{'b} } -->
   sequent ['ext] { 'H; x: eq{pair{'a; 'b}; pair{'z; 'z}}; 'J['x]; y: eq{'a; 'b} >- 'C['x]} -->
   sequent ['ext] { 'H; x: eq{pair{'a; 'b}; pair{'z; 'z}}; 'J['x] >- 'C['x] }

interactive equiv_equal_elim {| elim [] |} 'H 'J :
   sequent [squash] { 'H; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); 'J['x] >- isset{'a} } -->
   sequent [squash] { 'H; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); 'J['x] >- isset{'b} } -->
   sequent ['ext] { 'H; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); 'J['x] >- mem{'a; 's} } -->
   sequent ['ext] { 'H; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); 'J['x] >- mem{'b; 's} } -->
   sequent ['ext] { 'H; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); 'J['x]; y: equal{'a; 'b} >- 'C['x] } -->
   sequent ['ext] { 'H; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); 'J['x] >- 'C['x] }
