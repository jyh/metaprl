include Itt_equal
include Itt_rfun
include Itt_logic
include Itt_bool

open Printf
open Mp_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Rformat
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_meta
open Base_dtactic

open Itt_equal
open Itt_struct
(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare int
declare number[n:n]
declare ind{'i; m, z. 'down; 'base; m, z. 'up}

declare "add"{'a; 'b}
declare uni_minus{'a}

declare beq_int{'a; 'b}
declare lt_bool{'a; 'b}

prim add_wf 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- 'a +@ 'b = 'a1 +@ 'b1 in int } = it

prim uni_wf 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   sequent ['ext] { 'H >- uni_minus{'a} = uni_minus{'a1} in int } = it

prim lt_bool_wf 'H :
   sequent [squash] { 'H >- 'a='a1 in int } -->
   sequent [squash] { 'H >- 'b='b1 in int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} = lt_bool{'a1; 'b1} in bool } = it

(* Derived from previous *)
interactive lt_bool_wf2 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} IN bool }

prim beq_wf 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- beq_int{'a; 'b} = beq_int{'a1; 'b1} in bool } = it

prim beq_int2prop 'H :
   [main] sequent [squash] { 'H >- "assert"{beq_int{'a; 'b}} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a = 'b in int } = it

(* Derived from previous *)
interactive eq_int_assert_elim 'H 'J :
   [main] sequent ['ext] { 'H; x: 'a = 'b in int; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{beq_int{'a; 'b}}; 'J['x] >- 'C['x] }

(*
rewrite beq_int_is_true 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- beq_int{'a; 'b} <--> "btrue" }
*)
prim_rw beq_int_is_true 'H :
   ('a = 'b in int) -->
   beq_int{'a; 'b} <--> btrue

(*
 Derived from previous rewrite
 *)
interactive eq_2beq_int 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- "assert"{beq_int{'a; 'b}} }

(*
 Prop-int-lt definition
 *)

declare lt{'a; 'b}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Reduction on induction combinator:
 * Three cases:
 *    let ind[x] = ind(x; i, j. down[i, j]; base; k, l. up[k, l]
 *    x < 0 => (ind[x] -> down[x, ind[x + 1]]
 *    x = 0 => (ind[x] -> base)
 *    x > 0 => (ind[x] -> up[x, ind[x - 1]]
 *)
prim_rw reduce_ind_down :
   ('x < 0) -->
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
    ('down['x; ind{('x +@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

prim_rw reduce_ind_up :
   (0 < 'x) -->
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
   ('up['x; ind{('x -@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

prim_rw reduce_ind_base :
   (ind{0; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) <-->
   'base

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Z
 * by intFormation
 *)
prim intFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] } = int

(*
 * H >- int Type
 *)
prim intType 'H :
   sequent ['ext] { 'H >- "type"{int} } = it

(*
 * H >- Z = Z in Ui ext Ax
 * by intEquality
 *)
prim intEquality 'H :
   sequent ['ext] { 'H >- int = int in univ[i:l] } = it

(*
 * H >- Z ext n
 * by numberFormation n
 *)
prim numberFormation 'H number[n:n] :
   sequent ['ext] { 'H >- int } = number[n:n]

(*
 * H >- i = i in int
 * by numberEquality
 *)
prim numberEquality 'H :
   sequent ['ext] { 'H >- number[n:n] = number[n:n] in int } = it

(*
 * Induction:
 * H, n:Z, J[n] >- C[n] ext ind(i; m, z. down[n, m, it, z]; base[n]; m, z.
up[n, m, it, z])
 * by intElimination [m; v; z]
 *
 * H, n:Z, J[n], m:Z, v: m < 0, z: C[m + 1] >- C[m] ext down[n, m, v, z]
 * H, n:Z, J[n] >- C[0] ext base[n]
 * H, n:Z, J[n], m:Z, v: 0 < m, z: C[m - 1] >- C[m] ext up[n, m, v, z]
 *)
prim intElimination 'H 'J 'n 'm 'v 'z :
   sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 'm < 0; z: 'C['m +@ 1] >- 'C['m] } -->
   sequent ['ext] { 'H; n: int; 'J['n] >- 'C[0] } -->
   sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 0 < 'm; z: 'C['m -@ 1] >- 'C['m] } -->
   sequent ['ext] { 'H; n: int; 'J['n] >- 'C['n] } =
      ind{'n; m, z. 'down['n; 'm; it; 'z]; 'base['n]; m, z. 'up['n; 'm; it;
'z]}

(*
 * Equality on induction combinator:
 * let a = ind(x1; i1, j1. down1[i1, j1]; base1; k1, l1. up1[k1, l1])
 * let b = ind(x2; i2, j2. down2[i2, j2]; base2; k2, l2. up2[k2, l2])
 *
 * H >- a = b in T[x1]
 * by indEquality [z. T[z]; x; y; w]
 *
 * H >- x1 = y1 in Z
 * H, x: Z, w: x < 0, y: T[x + 1] >- down1[x, y] = down2[x, y] in T[x]
 * H >- base1 = base2 in T[0]
 * H, x: Z, w: 0 < x, y: T[x - 1] >- up1[x, y] = up2[x, y] in T[x]
 *)
prim indEquality 'H lambda{z. 'T['z]} 'x 'y 'w :
   sequent [squash] { 'H >- 'x1 = 'x2 in int } -->
   sequent [squash] { 'H; x: int; w: 'x < 0; y: 'T['x add 1] >- 'down1['x; 'y] = 'down2['x; 'y] in 'T['x] } -->
   sequent [squash] { 'H >- 'base1 = 'base2 in 'T[0] } -->
   sequent [squash] { 'H; x: int; w: 0 < 'x; y: 'T['x sub 1] >- 'up1['x; 'y] = 'up2['x; 'y] in 'T['x] } -->
   sequent ['ext] { 'H >- ind{'x1; i1, j1. 'down1['i1; 'j1]; 'base1; k1, l1. 'up1['k1; 'l1]}
                   = ind{'x2; i2, j2. 'down2['i2; 'j2]; 'base2; k2, l2. 'up2['k2; 'l2]}
                   in 'T['x1] } =
   it


(*
 Definition of basic operations (and relations) on int
 *)

prim_rw lt_Reflex 'H:
   ('a IN int) -->
   ('b IN int) -->
   band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} <--> bfalse

prim_rw lt_Trichot 'H:
   ('a IN int ) -->
   ('b IN int ) -->
   bor{bor{lt_bool{'a; 'b};lt_bool{'b; 'a}}; beq_int{'a; 'b}} <--> btrue

(*
Switching to rewrite to provide the uniform of int-properties

rule lt_Transit 'H 'b:
   sequent [squash] { 'H >- 'a < 'b } -->
   sequent [squash] { 'H >- 'b < 'c } -->
   sequent ['ext] { 'H >- 'a < 'c }
*)

prim_rw lt_Transit 'H 'b :
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   (band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool) -->
   lt_bool{'a; 'c} <--> btrue

prim_rw lt_Discret 'H:
   ('a IN int ) -->
   ('b IN int ) -->
   lt_bool{'a; 'b} <--> bor{beq_int{('a +@ 1); 'b}; lt_bool{('a +@ 1); 'b}}

prim_rw lt_addMono 'H 'c:
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('a +@ 'c); ('b +@ 'c)}

prim_rw add_Commut 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('a +@ 'b) <--> ('b +@ 'a)

prim_rw add_Assoc 'H:
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ('a +@ ('b +@ 'c)) <--> (('a +@ 'b) +@ 'c)

prim_rw add_Id 'H :
   ('a IN int ) -->
   'a <--> ('a +@ 0) 

prim_rw uni_add_inverse 'H :
   ('a IN int ) -->
   ( 'a +@ uni_minus{ 'a } ) <--> 0 

(*
rewrite sub_reduce 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a -@ 'b <--> 'a +@ uni_minus{'b}
*)

declare "sub"{'a ; 'b}

prim_rw unfold_sub :
   "sub"{'a ; 'b} <--> ('a +@ uni_minus{'b})

interactive_rw uni_add_Distrib 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   uni_minus{ ('a +@ 'b) } <--> ( uni_minus{ 'b } +@ uni_minus{ 'b } ) 

interactive_rw uni_uni_reduce 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   uni_minus{ uni_minus{ 'a } } <--> 'a
















