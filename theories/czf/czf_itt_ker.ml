include Czf_itt_group
include Czf_itt_subgroup
include Czf_itt_group_bvd
include Czf_itt_hom
include Czf_itt_sep
include Czf_itt_inv_image
include Czf_itt_coset
include Czf_itt_normal_subgroup

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

declare ker{'h; 'g1; 'g2; x. 'f['x]}

dform ker_df : parens :: except_mode[src] :: ker{'h; 'g1; 'g2; x. 'f} =
   `"ker(" slot{'h} `"; " slot{'g1} `"; " slot{'g2} `"; " slot{'f} `")"

(*
 * f is a homomorphism of g1 into g2. The elements of g1,
 * which are mapped into the identity of g2, form a subgroup
 * h of g called the ker of f.
 *)
prim_rw unfold_ker : ker{'h; 'g1; 'g2; x. 'f['x]} <-->
   (hom{'g1; 'g2; x. 'f['x]} & group_bvd{'h; 'g1; sep{car{'g1}; x. mem{pair{'f['x]; id{'g2}}; eqG{'g2}}}})

(*
 * Properties for kers.
 *)
interactive ker_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- "type"{ker{'h; 'g1; 'g2; x. 'f['x]}} }

interactive ker_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- group_bvd{'h; 'g1; sep{car{'g1}; x. mem{pair{'f['x]; id{'g2}}; eqG{'g2}}}} } -->
   sequent ['ext] { 'H >- ker{'h; 'g1; 'g2; x. 'f['x]} }

interactive ker_equiv {| elim [] |} 'H 'J 'y :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- isset{'y} } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- ker{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- mem{'y; car{'h}} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: mem{'y; car{'g1}}; w: equiv{car{'g2}; eqG{'g2}; 'f['y]; id{'g2}} >- 'C['u] } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

(*
 * Let f: G -> G' be a group homomorphism of G into G'.
 * The ker of f is a subgroup of G.
 *)
interactive ker_subgroup 'H hom{'g1; 'g2; x. 'f['x]} 'h :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent ['ext] { 'H >- ker{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g1} }

interactive ker_subgroup_elim (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: subgroup{'h; 'g1} >- 'C['u] } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

let kerSubgT i p =
   let j, k = Sequent.hyp_indices p i in
      ker_subgroup_elim j k p

(*
 * Let f: G1 -> G2 be a group homomorphism of G1 into G2.
 * Let H be the ker of f. For any a in G1, the set
 * { x in G1 | f(x) = f(a) } is the left coset aH of H.
 *)
interactive ker_lcoset {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- ker{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- equal{sep{car{'g1}; x. mem{pair{'f['x]; 'f['a]}; eqG{'g2}}}; lcoset{'h; 'g1; 'a}} }

interactive ker_lcoset1 (*{| elim [] |}*) 'H 'J 'a :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- isset{'a} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: equal{sep{car{'g1}; x. mem{pair{'f['x]; 'f['a]}; eqG{'g2}}}; lcoset{'h; 'g1; 'a}} >- 'C['u] } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

let kerLcosetT t i p =
   let j, k = Sequent.hyp_indices p i in
      ker_lcoset1 j k t p

(*
 * Let f: G1 -> G2 be a group homomorphism of G1 into G2.
 * Let H be the ker of f. For any a in G1, the set
 * { x in G1 | f(x) = f(a) } is also the right coset Ha of H.
 *)
interactive ker_rcoset {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- ker{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- equal{sep{car{'g1}; x. mem{pair{'f['x]; 'f['a]}; eqG{'g2}}}; rcoset{'h; 'g1; 'a}} }

interactive ker_rcoset1 (*{| elim [] |}*) 'H 'J 'a :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- isset{'a} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: equal{sep{car{'g1}; x. mem{pair{'f['x]; 'f['a]}; eqG{'g2}}}; rcoset{'h; 'g1; 'a}} >- 'C['u] } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

let kerRcosetT t i p =
   let j, k = Sequent.hyp_indices p i in
      ker_rcoset1 j k t p

(*
 * A group homomorphism f: G1 -> G2 is a one-to-one map
 * if and only if Ker(f) = {id(g1)}.
 *)
interactive ker_injection1 (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- equal{car{'h}; sep{car{'g1}; x. mem{pair{'x; id{'g1}}; eqG{'g1}}}} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- all c: set.all d: set. (mem{'c; car{'g1}} => mem{'d; car{'g1}} => equiv{car{'g2}; eqG{'g2}; 'f['c]; 'f['d]} => equiv{car{'g1}; eqG{'g1}; 'c; 'd}) }

interactive ker_injection2 (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; c: set; d: set; u: mem{'c; car{'g1}}; v: mem{'d; car{'g1}}; w: equiv{car{'g2}; eqG{'g2}; 'f['c]; 'f['d]} >- equiv{car{'g1}; eqG{'g1}; 'c; 'd} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- equal{car{'h}; sep{car{'g1}; x. mem{pair{'x; id{'g1}}; eqG{'g1}}}} }

(*
 * The ker of a homomorphism f: G1 -> G2 is a normal subgroup of G1.
 *)
interactive ker_normalSubg (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: normal_subg{'h; 'g1} >- 'C['u] } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

let kerNormalSubgT i p =
   let j, k = Sequent.hyp_indices p i in
      ker_normalSubg j k p
