(*
 * Int is the type of tokens (strings)
 *
 *)

include Tactic_type

include Itt_equal
include Itt_rfun
include Itt_logic

open Refiner.Refiner.Term

open Tactic_type

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare int
declare natural_number[@n:n]
declare ind{'i; m, z. 'down; 'base; m, z. 'up}

val int_term : term
val zero : term

declare "add"{'a; 'b}
declare "sub"{'a; 'b}
declare "mul"{'a; 'b}
declare "div"{'a; 'b}
declare "rem"{'a; 'b}
declare lt{'a; 'b}
declare le{'a; 'b}
declare ge{'a; 'b}
declare gt{'a; 'b}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_compare
prec prec_add
prec prec_mul

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reduceLE  : le{'a; 'b} <--> ('a < 'b or 'a = 'b in int)
rewrite reduceGT  : gt{'a; 'b} <--> 'b < 'a
rewrite reduceGE  : ge{'a; 'b} <--> ('b < 'a or 'a = 'b in int)

rewrite reduceAdd : "add"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i + @j]
rewrite reduceSub : "sub"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i - @j]
rewrite reduceMul : "mul"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i * @j]
rewrite reduceDiv : "div"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i / @j]
rewrite reduceRem : "rem"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i % @j]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
(*
 * Reduction on induction combinator:
 * Three cases:
 *    let ind[x] = ind(x; i, j. down[i, j]; base; k, l. up[k, l]
 *    x < 0 => (ind[x] -> down[x, ind[x + 1]]
 *    x = 0 => (ind[x] -> base)
 *    x > 0 => (ind[x] -> up[x, ind[x - 1]]
 *)
rewrite indReduceDown :
   'x < 0 -->
   ((ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) <-->
    'down['x; ind{('x +@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

rewrite indReduceUp :
   ('x > 0) -->
   (ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
    'up['x; ind{('x -@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

rewrite indReduceBase :
   (ind{0; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) <-->
   'base

mlterm indReduce{ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}}
rewrite indReduce : ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
   indReduce{ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}}
*)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Z
 * by intFormation
 *)
axiom intFormation 'H : sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- Z = Z in Ui ext Ax
 * by intEquality
 *)
axiom intEquality 'H : sequent ['ext] { 'H >- int = int in univ[@i:l] }

(*
 * H >- Z ext n
 * by numberFormation n
 *)
axiom numberFormation 'H natural_number[@n:n] : sequent ['ext] { 'H >- int }

(*
 * Induction:
 * H, n:Z, J[n] >- C[n] ext ind(i; m, z. down[n, m, it, z]; base[n]; m, z. up[n, m, it, z])
 * by intElimination [m; v; z]
 *
 * H, n:Z, J[n], m:Z, v: m < 0, z: C[m + 1] >- C[m] ext down[n, m, v, z]
 * H, n:Z, J[n] >- C[0] ext base[n]
 * H, n:Z, J[n], m:Z, v: 0 < m, z: C[m - 1] >- C[m] ext up[n, m, v, z]
 *)
axiom intElimination 'H 'J 'n 'm 'v 'z :
   sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 'm < 0; z: 'C['m add 1] >- 'C['m] } -->
   sequent ['ext] { 'H; n: int; 'J['n] >- 'C[0] } -->
   sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 0 < 'm; z: 'C['m sub 1] >- 'C['m] } -->
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
axiom indEquality 'H lambda{z. 'T['z]} 'x 'y 'w :
   sequent [squash] { 'H >- 'x1 = 'x2 in int } -->
   sequent [squash] { 'H; x: int; w: 'x < 0; y: 'T['x add 1] >- 'down1['x; 'y] = 'down2['x; 'y] in 'T['x] } -->
   sequent [squash] { 'H >- 'base1 = 'base2 in 'T[0] } -->
   sequent [squash] { 'H; x: int; w: 'x > 0; y: 'T['x sub 1] >- 'up1['x; 'y] = 'up2['x; 'y] in 'T['x] } -->
   sequent ['ext] { 'H >- ind{'x1; i1, j1. 'down1['i1; 'j1]; 'base1; k1, l1. 'up1['k1; 'l1]}
                   = ind{'x2; i2, j2. 'down2['i2; 'j2]; 'base2; k2, l2. 'up2['k2; 'l2]}
                   in 'T['x1] }

(*
 * less_thanFormation:
 * H >- Ui ext a < b
 * by less_thanFormation
 *
 * H >- Z ext a
 * H >- Z ext b
 *)
axiom less_thanFormation 'H :
   sequent ['ext] { 'H >- int } -->
   sequent ['ext] { 'H >- int } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- i1 < j1 = i2 < j2 in Ui
 * by less_thanEquality
 *
 * H >- i1 = j1 in int
 * H >- i2 = j2 in int
 *)
axiom less_thanEquality 'H :
   sequent [squash] { 'H >- 'i1 = 'j1 in int } -->
   sequent [squash] { 'H >- 'i2 = 'j2 in int } -->
   sequent ['ext] { 'H >- 'i1 < 'j1 = 'i2 < 'j2 in univ[@i:l] }

(*
 * H >- it = it in (a < b)
 * by less_than_memberEquality
 *
 * H >- a < b
 *)
axiom less_than_memberEquality 'H :
    sequent [squash] { 'H >- 'a < 'b } -->
    sequent ['ext] { 'H >- it = it in ('a < 'b) }

(*
 * H, x: a < b, J[x] >- C[x]
 * by less_than_Elimination i
 *
 * H, x: a < b; J[it] >- C[it]
 *)
axiom less_thanElimination 'H 'J :
   sequent ['ext] { 'H; x: 'a < 'b; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: 'a < 'b; 'J['x] >- 'C['x] }

(*
 * H >- i = j in Z
 * by arith
 *
 * This is computed with a side condition.
 *)
mlterm arith_check{'t}
axiom arith : arith_check{'t} --> 't

(*
val x : (d_resource_info, d_tactic, d_data) Resource.rsrc
*)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_intT : int -> tactic
val eqcd_intT : tactic

val int_term : term

val natural_number_term : term
val is_natural_number_term : term -> bool
val dest_natural_number : term -> Num.num
val mk_natural_number_term : Num.num -> term

val ind_term : term
val is_ind_term : term -> bool
val dest_ind : term -> term * string * string * term * term * string * string * term
val mk_ind_term : term -> string -> string -> term -> term -> string -> string -> term -> term

(*
 * $Log$
 * Revision 1.5  1998/05/28 13:47:39  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.4  1998/04/22 22:44:49  jyh
 * *** empty log message ***
 *
 * Revision 1.3  1998/04/09 18:26:05  jyh
 * Working compiler once again.
 *
 * Revision 1.2  1997/08/06 16:18:32  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:13  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.8  1996/10/23 15:18:08  jyh
 * First working version of dT tactic.
 *
 * Revision 1.7  1996/09/25 22:52:12  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.6  1996/09/02 19:37:25  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.5  1996/05/21 02:16:50  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.4  1996/04/11 13:34:02  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.3  1996/03/28 02:51:32  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.2  1996/03/05 19:59:48  jyh
 * Version just before LogicalFramework.
 *
 * Revision 1.1  1996/02/13 21:36:01  jyh
 * Intermediate checkin while matching is bing added to the refiner.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
