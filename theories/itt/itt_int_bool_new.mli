include Itt_equal
include Itt_rfun
include Itt_logic
include Itt_bool

open Refiner.Refiner.Term

open Tactic_type.Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare int
declare number[n:n]
declare ind{'i; m, z. 'down; 'base; m, z. 'up}

declare "add"{'a; 'b}
declare uni_minus{'a}
(*
   declare "sub"{'a; 'b}
*)
declare "mul"{'a; 'b}
declare "div"{'a; 'b}
declare "rem"{'a; 'b}

declare beq_int{'a; 'b}
declare lt_bool{'a; 'b}

rule add_wf 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- 'a +@ 'b = 'a1 +@ 'b1 in int }

rule mul_wf 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- 'a *@ 'b = 'a1 *@ 'b1 in int }

rule uni_wf 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   sequent ['ext] { 'H >- uni_minus{'a} = uni_minus{'a1} in int }

(*
А такие подцели - это main, wf или еще что-то ?
*)
rule lt_bool_wf 'H :
   sequent [squash] { 'H >- 'a='a1 in int } -->
   sequent [squash] { 'H >- 'b='b1 in int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} = lt_bool{'a1; 'b1} in bool }

(* Derived from previous *)
rule lt_bool_wf2 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} IN bool }

(*
 Definitions of >b <=b >=b
 *)

define unfold_gt_bool :
   gt_bool{'a; 'b} <--> lt_bool{'b; 'a}

define unfold_le_bool :
   le_bool{'a; 'b} <--> bnot{lt_bool{'b; 'a}}

define unfold_ge_bool :
   ge_bool{'a; 'b} <--> bnot{lt_bool{'a; 'b}}

(*
 = in int VS beq_int
 *)

rule beq_wf 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- beq_int{'a; 'b} = beq_int{'a1; 'b1} in bool }

rule beq_int2prop 'H :
   [main] sequent [squash] { 'H >- "assert"{beq_int{'a; 'b}} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a = 'b in int }

(* Derived from previous *)
rule eq_int_assert_elim 'H 'J :
   [main] sequent ['ext] { 'H; x: 'a = 'b in int; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{beq_int{'a; 'b}}; 'J['x] >- 'C['x] }

(*
rewrite beq_int_is_true 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- beq_int{'a; 'b} <--> "btrue" }
*)
rewrite beq_int_is_true 'H :
   ('a = 'b in int) -->
   beq_int{'a; 'b} <--> btrue

(*
 Derived from previous rewrite
 *)
rule eq_2beq_int 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- "assert"{beq_int{'a; 'b}} }

define unfold_bneq_int :
   bneq_int{'a; 'b} <--> bnot{beq_int{'a; 'b}}

(*
 Prop-int-relations definitions
 *)

define unfold_lt :
   lt{'a; 'b} <--> "assert"{lt_bool{'a; 'b}}

define unfold_gt :
   gt{'a; 'b} <--> 'b < 'a

(*
Switching to define-version to provide the same behaviour as bool-relations,
i.d. rewritability of <= in the same extent as of <

rewrite unfold_le 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a <= 'b <--> ('a < 'b) \/ ('a = 'b in int) }

rewrite unfold_ge 'H :
   [wf] sequent [squash] { 'H >- a IN int } -->
   [wf] sequent [squash] { 'H >- b IN int } -->
   sequent ['ext] { 'H >- 'a >= 'b <--> ('a < 'b) \/ ('a = 'b in int) }
*)

define unfold_le :
   le{'a; 'b} <--> "assert"{le_bool{'a; 'b}}

define unfold_ge :
   ge{'a; 'b} <--> 'b <= 'a

define unfold_neq_int :
   nequal{'a; 'b} <--> "assert"{bneq_int{'a; 'b}}

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
rewrite reduce_ind_down :
   ('x < 0) -->
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
    ('down['x; ind{('x +@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

rewrite reduce_ind_up :
   ('x > 0) -->
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
   ('up['x; ind{('x -@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

rewrite reduce_ind_base :
   (ind{0; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) <-->
   'base

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Z
 * by intFormation
 *)
rule intFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H >- int Type
 *)
rule intType 'H :
   sequent ['ext] { 'H >- "type"{int} }

(*
 * H >- Z = Z in Ui ext Ax
 * by intEquality
 *)
rule intEquality 'H :
   sequent ['ext] { 'H >- int = int in univ[i:l] }

(*
 * H >- Z ext n
 * by numberFormation n
 *)
rule numberFormation 'H number[n:n] :
   sequent ['ext] { 'H >- int }

(*
 * H >- i = i in int
 * by numberEquality
 *)
rule numberEquality 'H :
   sequent ['ext] { 'H >- number[n:n] = number[n:n] in int }

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
rule intElimination 'H 'J 'n 'm 'v 'z :
   sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 'm < 0; z: 'C['m +@ 1] >- 'C['m] } -->
   sequent ['ext] { 'H; n: int; 'J['n] >- 'C[0] } -->
   sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 0 < 'm; z: 'C['m -@ 1] >- 'C['m] } -->
   sequent ['ext] { 'H; n: int; 'J['n] >- 'C['n] }

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
rule indEquality 'H lambda{z. 'T['z]} 'x 'y 'w :
   sequent [squash] { 'H >- 'x1 = 'x2 in int } -->
   sequent [squash] { 'H; x: int; w: 'x < 0; y: 'T['x add 1] >- 'down1['x; 'y] = 'down2['x; 'y] in 'T['x] } -->
   sequent [squash] { 'H >- 'base1 = 'base2 in 'T[0] } -->
   sequent [squash] { 'H; x: int; w: 'x > 0; y: 'T['x sub 1] >- 'up1['x; 'y] = 'up2['x; 'y] in 'T['x] } -->
   sequent ['ext] { 'H >- ind{'x1; i1, j1. 'down1['i1; 'j1]; 'base1; k1, l1. 'up1['k1; 'l1]}
                   = ind{'x2; i2, j2. 'down2['i2; 'j2]; 'base2; k2, l2. 'up2['k2; 'l2]}
                   in 'T['x1] }


(*
 Definition of basic operations (and relations) on int
 *)

rewrite lt_Reflex 'H:
   ('a IN int) -->
   ('b IN int) -->
   band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} <--> bfalse

rewrite lt_Trichot 'H:
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

rewrite lt_Transit 'H 'b :
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   (band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool) -->
   lt_bool{'a; 'c} <--> btrue

rewrite lt_Discret 'H:
   ('a IN int ) -->
   ('b IN int ) -->
   lt_bool{'a; 'b} <--> bor{beq_int{('a +@ 1); 'b}; lt_bool{('a +@ 1); 'b}}

rewrite lt_addMono 'H 'c:
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('a +@ 'c); ('b +@ 'c)}

rewrite lt_mulPositMono 'H 'c:
   (0 < 'c ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('c *@ 'a); ('c *@ 'b) }

rewrite add_Commut 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('a +@ 'b) <--> ('b +@ 'a)

rewrite add_Assoc 'H:
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ('a +@ ('b +@ 'c)) <--> (('a +@ 'b) +@ 'c)

rewrite mul_Commut 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('a *@ 'b) <--> ('b *@ 'a)

rewrite mul_Assoc 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ('a *@ ('b *@ 'c)) <--> (('a *@ 'b) *@ 'c) 

rewrite mul_add_Distrib 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ('a *@ ('b +@ 'c)) <--> (('a *@ 'b) +@ ('a *@ 'c)) 

rewrite add_Id 'H :
   ('a IN int ) -->
   'a <--> ('a +@ 0) 

rewrite mul_Id 'H :
   ('a IN int ) -->
   'a <--> (1 *@ 'a) 

rewrite mul_Zero 'H :
   ('a IN int ) -->
   (0 *@ 'a) <--> 0
 
rewrite uni_add_inverse 'H :
   ('a IN int ) -->
   ( 'a +@ uni_minus{ 'a } ) <--> 0 

(*
rewrite sub_reduce 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a -@ 'b <--> 'a +@ uni_minus{'b}
*)

define unfold_sub :
   "sub"{'a ; 'b} <--> ('a +@ uni_minus{'b})

rewrite uni_add_Distrib 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   uni_minus{ ('a +@ 'b) } <--> ( uni_minus{ 'b } +@ uni_minus{ 'b } ) 

rewrite uni_uni_reduce 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   uni_minus{ uni_minus{ 'a } } <--> 'a

rewrite mul_uni_Assoc 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('a *@ uni_minus{ 'b }) <--> (uni_minus{ 'a } *@ 'b)

(*думаю для этого преобразования понадобится определение uni-*)
rewrite lt_mulNegMono 'H 'c:
   ('c < 0 ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('c *@ 'b) ; ('c *@ 'a)} 

rewrite rem_baseReduce 'H:
   (0 <= 'a ) -->
   ('a < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('a rem 'b) <--> 'a 

rewrite rem_indReduce 'H:
   (0 < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ((('a *@ 'b) +@ 'c) rem 'b) <--> ('c rem 'b) 

rule rem_wf 'H :
   sequent [squash] { 'H >- "nequal"{'b ; 0} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- ('a rem 'b) IN int }

rewrite div_baseReduce 'H:
   (0 <= 'a ) -->
   ('a < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('a /@ 'b) <--> 0

rewrite div_indReduce 'H:
   (0 < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ((('a *@ 'b) +@ 'c) /@ 'b) <--> ('a +@ ('c /@ 'b)) 

rule div_wf 'H :
   sequent [squash] { 'H >- "nequal"{'b ; 0} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a /@ 'b IN int }

rule lt_divMono 'H 'b :
   sequent [squash] { 'H >- 0 < 'c } -->
   sequent [squash] { 'H >- 'a < 'b } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- 'a /@ 'c <= 'b /@ 'c }

rule add_divReduce 'H:
   sequent [squash] {'H >- 0 < 'a } -->
   sequent [squash] {'H >- 0 < 'b } -->
   sequent [squash] {'H >- 0 < 'c } -->
   [wf] sequent [squash] {'H >- 'a IN int } -->
   [wf] sequent [squash] {'H >- 'b IN int } -->
   [wf] sequent [squash] {'H >- 'c IN int } -->
   sequent ['ext] {'H >- ('a /@ 'c) +@ ('b /@ 'c) <= ('a +@ 'b) /@ 'c }

rewrite div_Assoc 'H:
   (0 <= 'a ) -->
   (0 < 'b ) -->
   (0 < 'c ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   (('a /@ 'b) /@ 'c) <--> ('a /@ ('b *@ 'c))

(*
Incorrect but there has to be some assoc/commut/composition property

rewrite rem_Assoc 'H:
   sequent [squash] { 'H >- 0 <= 'a } -->
   sequent [squash] { 'H >- 0 < 'b } -->
   sequent [squash] { 'H >- 0 < 'c } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- ('a rem 'b) rem 'c <--> ('a rem 'c) rem 'b }

*)


