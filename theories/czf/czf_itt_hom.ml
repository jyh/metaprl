include Czf_itt_group
include Czf_itt_subgroup
include Czf_itt_abel_group
include Czf_itt_equiv
include Czf_itt_group_bvd
include Czf_itt_set_bvd
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

declare hom{'g1; 'g2; x. 'f['x]}
declare kernel{'h; 'g1; 'g2; x. 'f['x]}

dform hom_df : parens :: except_mode[src] :: hom{'g1; 'g2; x. 'f} =
   `"hom(" slot{'g1} `"; " slot{'g2} `"; " slot{'f} `")"

dform kernel_df : parens :: except_mode[src] :: kernel{'h; 'g1; 'g2; x. 'f} =
   `"kernel(" slot{'h} `"; " slot{'g1} `"; " slot{'g2} `"; " slot{'f} `")"

(*
 * g1 and g2 are groups; f is a map of g1 into g2;
 * and for all a, b in g1, f(a * b) = f(a) * f(b).
 *)
prim_rw unfold_hom : hom{'g1; 'g2; x. 'f['x]} <-->
   (group{'g1} & group{'g2} & (all a: set. (mem{'a; car{'g1}} => mem{'f['a]; car{'g2}})) & (all a: set. all b: set. (mem{'a; car{'g1}} => mem{'b; car{'g1}} => equiv{car{'g1}; eqG{'g1}; 'a; 'b} => equiv{car{'g2}; eqG{'g2}; 'f['a]; 'f['b]})) & (all a: set. all b: set. (mem{'a; car{'g1}} => mem{'b; car{'g1}} => equiv{car{'g2}; eqG{'g2}; 'f[op{'g1; 'a; 'b}]; op{'g2; 'f['a]; 'f['b]}})))

(*
 * f is a homomorphism of g1 into g2. The elements of g1,
 * which are mapped into the identity of g2, form a subgroup
 * h of g called the kernel of f.
 *)
prim_rw unfold_kernel : kernel{'h; 'g1; 'g2; x. 'f['x]} <-->
   (hom{'g1; 'g2; x. 'f['x]} & group_bvd{'h; 'g1; setbvd_prop{car{'g1}; x. equiv{car{'g2}; eqG{'g2}; 'f['x]; id{'g2}}}})

interactive hom_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H; x: set >- isset{'f['x]} } -->
   sequent ['ext] { 'H >- "type"{hom{'g1; 'g2; x. 'f['x]}} }

interactive hom_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent ['ext] { 'H; x: set; y: mem{'x; car{'g1}} >- mem{'f['x]; car{'g2}} } -->
   sequent ['ext] { 'H; c: set; d: set; x1: mem{'c; car{'g1}}; y1: mem{'d; car{'g1}}; u: equiv{car{'g1}; eqG{'g1}; 'c; 'd} >- equiv{car{'g2}; eqG{'g2}; 'f['c]; 'f['d]} } -->
   sequent ['ext] { 'H; e: set; g: set; x2: mem{'e; car{'g1}}; y2: mem{'g; car{'g1}} >- equiv{car{'g2}; eqG{'g2}; 'f[op{'g1; 'e; 'g}]; op{'g2; 'f['e]; 'f['g]}} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} }

interactive hom_fun {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent ['ext] { 'H; z: set; x1: set; y1: mem{'x1; car{'g1}} >- mem{'f['z; 'x1]; car{'g2}} } -->
   sequent ['ext] { 'H; z: set >- fun_set{x. 'f['x; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. hom{'g1; 'g2; y. 'f['z; 'y]}} }

interactive hom_equiv_fun {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent [squash] { 'H; z: set; x: set >- isset{'f['z; 'x]} } -->
   sequent ['ext] { 'H; z1: set; x1: set; y1: mem{'x1; car{'g1}} >- mem{'f['z1; 'x1]; car{'g2}} } -->
   sequent ['ext] { 'H; z3: set; c: set; d: set; x3: mem{'c; car{'g1}}; y3: mem{'d; car{'g1}}; v: equiv{car{'g1}; eqG{'g1}; 'c; 'd} >- equiv{car{'g2}; eqG{'g2}; 'f['c; 'z3]; 'f['d; 'z3]} } -->
   sequent ['ext] { 'H >- equiv_fun_prop{car{'g1}; eqG{'g1}; z. hom{'g1; 'g2; y. 'f['z; 'y]}} }

(*
 * Trivial homomorphism
 * For any groups G and G', there is always at least one homomorphism
 * f: G - >G' defined by 'f('a) = e' for all a in G, where e' is the
 * identity in G'. This is called the trivial homomorphism.
 *)
interactive trivial_hom 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent ['ext] { 'H; x: set; y: mem{'x; car{'g1}} >- equiv{car{'g2}; eqG{'g2}; 'f['x]; id{'g2}} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} }

(*
 * Let f: G -> G' be a group homomorphism of G ONTO G'. If G is abelian,
 * then G' must be abelian.
 *)
interactive hom_abel 'H hom{'g1; 'g2; x. 'f['x]} :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H; x: set; y: mem{'x; car{'g2}} >- exst z: set. (mem{'z; car{'g1}} & equiv{car{'g2}; eqG{'g2}; 'x; 'f['z]}) } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- abel{'g1} } -->
   sequent ['ext] { 'H >- abel{'g2} }

(*
 * properties
 *)
(*
 * Let f: G -> G' be a group homomorphism of G into G'.
 * If e is the identity in G, then f(e) is the identity e' in G'.
 *)
interactive hom_id {| intro [] |} 'H hom{'g1; 'g2; x. 'f['x]} :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- equiv{car{'g2}; eqG{'g2}; 'f[id{'g1}]; id{'g2}} }

interactive hom_id_elim (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent ['ext] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u]; v: equiv{car{'g2}; eqG{'g2}; 'f[id{'g1}]; id{'g2}} >- 'C['u] } -->
   sequent ['ext] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

let homIdT i p =
   let j, k = Sequent.hyp_indices p i in
      hom_id_elim j k p

(*
 * Let f: G -> G' be a group homomorphism of G into G'.
 * For any a in G, f(inv(a)) = inv(f(a)).
 *)
interactive hom_inv {| intro [] |} 'H 'a hom{'g1; 'g2; x. 'f['x]} :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H >- equiv{car{'g2}; eqG{'g2}; 'f[inv{'g1; 'a}]; inv{'g2; 'f['a]}} }

interactive hom_inv_elim (*{| elim [] |}*) 'H 'J 'a :
   sequent [squash] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent [squash] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- isset{'a} } -->
   sequent ['ext] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u]; v: equiv{car{'g2}; eqG{'g2}; 'f[inv{'g1; 'a}]; inv{'g2; 'f['a]}} >- 'C['u] } -->
   sequent ['ext] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

let homInvT t i p =
   let j, k = Sequent.hyp_indices p i in
      hom_inv_elim j k t p

(*
 * Let f: G -> G' be a group homomorphism of G into G'.
 * If H is a subgroup of G, then f[H] is a subgroup of G'.
 *)
interactive hom_subgroup1 'H hom{'g1; 'g2; x. 'f['x]} 'h1 'h2 :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h1 IN label } -->
   sequent [squash] { 'H >- 'h2 IN label } -->
   sequent ['ext] { 'H >- group{'h2} } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- subgroup{'h1; 'g1} } -->
   sequent ['ext] { 'H >- group_bvd{'h2; 'g2; set_bvd{car{'h1}; x. 'f['x]}} } -->
   sequent ['ext] { 'H >- subgroup{'h2; 'g2} }

(*
 * Let f: G -> G' be a group homomorphism of G into G'.
 * If H is a subgroup of G', then the inverse image of
 * H is a subgroup of G.
 *)
interactive hom_subgroup2 'H hom{'g1; 'g2; x. 'f['x]} 'h1 'h2 :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h1 IN label } -->
   sequent [squash] { 'H >- 'h2 IN label } -->
   sequent ['ext] { 'H >- group{'h1} } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- subgroup{'h2; 'g2} } -->
   sequent ['ext] { 'H >- group_bvd{'h1; 'g1; inv_image{car{'g1}; x. 'f['x]; car{'h2}}} } -->
   sequent ['ext] { 'H >- subgroup{'h1; 'g1} }

(*
 * Properties for kernels.
 *)
interactive kernel_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H; x: set >- isset{'f['x]} } -->
   sequent ['ext] { 'H >- "type"{kernel{'h; 'g1; 'g2; x. 'f['x]}} }

interactive kernel_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- group_bvd{'h; 'g1; setbvd_prop{car{'g1}; x. equiv{car{'g2}; eqG{'g2}; 'f['x]; id{'g2}}}} } -->
   sequent ['ext] { 'H >- kernel{'h; 'g1; 'g2; x. 'f['x]} }

(*
 * Let f: G -> G' be a group homomorphism of G into G'.
 * The kernel of f is a subgroup of G.
 *)
interactive kernel_subgroup 'H hom{'g1; 'g2; x. 'f['x]} 'h :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent ['ext] { 'H >- kernel{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g1} }

interactive kernel_subgroup_elim (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: subgroup{'h; 'g1} >- 'C['u] } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

let kernelSubgroupT i p =
   let j, k = Sequent.hyp_indices p i in
      kernel_subgroup_elim j k p

(*
 * Let f: G1 -> G2 be a group homomorphism of G1 into G2.
 * Let H be the kernel of f. For any a in G1, the set
 * { x in G1 | f(x) = f(a) } is the left coset aH of H.
 *)
interactive kernel_lcoset {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- kernel{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- equal{setbvd_prop{car{'g1}; x. equiv{car{'g2}; eqG{'g2}; 'f['x]; 'f['a]}}; lcoset{'h; 'g1; 'a}} }

interactive kernel_lcoset1 (*{| elim [] |}*) 'H 'J 'a :
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- isset{'a} } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: equal{setbvd_prop{car{'g1}; x. equiv{car{'g2}; eqG{'g2}; 'f['x]; 'f['a]}}; lcoset{'h; 'g1; 'a}} >- 'C['u] } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

let kernelLcosetT t i p =
   let j, k = Sequent.hyp_indices p i in
      kernel_lcoset1 j k t p

(*
 * Let f: G1 -> G2 be a group homomorphism of G1 into G2.
 * Let H be the kernel of f. For any a in G1, the set
 * { x in G1 | f(x) = f(a) } is also the right coset Ha of H.
 *)
interactive kernel_rcoset {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- kernel{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- equal{setbvd_prop{car{'g1}; x. equiv{car{'g2}; eqG{'g2}; 'f['x]; 'f['a]}}; rcoset{'h; 'g1; 'a}} }

interactive kernel_rcoset1 (*{| elim [] |}*) 'H 'J 'a :
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- isset{'a} } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: equal{setbvd_prop{car{'g1}; x. equiv{car{'g2}; eqG{'g2}; 'f['x]; 'f['a]}}; rcoset{'h; 'g1; 'a}} >- 'C['u] } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

let kernelRcosetT t i p =
   let j, k = Sequent.hyp_indices p i in
      kernel_rcoset1 j k t p

(*
 * A group homomorphism f: G1 -> G2 is a one-to-one map
 * if and only if Ker(f) = {id(g1)}.
 *)
interactive kernel_injection1 (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- equal{car{'h}; setbvd_prop{car{'g1}; x. equiv{car{'g1}; eqG{'g1}; 'x; id{'g1}}}} } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- all c: set.all d: set. (mem{'c; car{'g1}} => mem{'d; car{'g1}} => equiv{car{'g2}; eqG{'g2}; 'f['c]; 'f['d]} => equiv{car{'g1}; eqG{'g1}; 'c; 'd}) }

interactive kernel_injection2 (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; c: set; d: set; u: mem{'c; car{'g1}}; v: mem{'d; car{'g1}}; w: equiv{car{'g2}; eqG{'g2}; 'f['c]; 'f['d]} >- equiv{car{'g1}; eqG{'g1}; 'c; 'd} } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- equal{car{'h}; setbvd_prop{car{'g1}; x. equiv{car{'g1}; eqG{'g1}; 'x; id{'g1}}}} }

(*
 * The kernel of a homomorphism f: G1 -> G2 is a normal subgroup of G1.
 *)
interactive kernel_normalSubg (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: normal_subg{'h; 'g1} >- 'C['u] } -->
   sequent ['ext] { 'H; u: kernel{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

let kernelNormalSubgT i p =
   let j, k = Sequent.hyp_indices p i in
      kernel_normalSubg j k p
