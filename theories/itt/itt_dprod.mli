(*
 * Rules for dependent product.
 *
 *)

include Tactic_type

include Itt_equal
include Itt_rfun

open Refiner.Refiner.Term

open Tactic_type

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(* declare prod{'A; 'B} *)
declare prod{'A; x. 'B['x]}
declare pair{'a; 'b}
declare spread{'e; u, v. 'b['u; 'v]}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_prod
prec prec_spread

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Reduction on spread:
 * spread(u, v; a, b. c[a, b]) <--> c[u, v]
 *)
rewrite reduceSpread : spread{'u, 'v; a, b. 'c['a; 'b]} <--> 'c['u; 'v]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext x:A # B
 * by productFormation A x
 * H >- A = A in Ui
 * H, x:A >- Ui ext B
 *)
axiom productFormation 'H 'A 'x :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   sequent ['ext] { 'H; x: 'A >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- x1:A1 # B1 = x2:A2 # B2 in Ui
 * by productEquality y
 * H >- A1 = A2 in Ui
 * H, y:A1 >- B1[y] = B2[y] in Ui
 *)
axiom productEquality 'H 'y :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[@i:l] } -->
   sequent ['ext] { 'H >- x1:'A1 * 'B1['x1] = x2:'A2 * 'B2['x2] in univ[@i:l] }

(*
 * H >- x:A * B ext (a, b)
 * by pairFormation a y
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
axiom pairFormation 'H 'a 'y :
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'B['a] } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- x:'A * 'B['x] }

(*
 * H >- (a1, b1) = (a2, b2) in x:A * B
 * by pairEquality y
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B[a1]
 * H, y:A >- B[y] = B[y] in Ui
 *)
axiom pairEquality 'H 'y :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B['a1] } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- ('a1, 'b1) = ('a2, 'b2) in x:'A * 'B }

(*
 * H, x:A * B[x], J[x] >- T[x] ext spread(x; u, v. t[u, v])
 * by productElimination u v
 * H, x:A * B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
axiom productElimination 'H 'J 'z 'u 'v :
   sequent ['ext] { 'H; z: x:'A * 'B['x]; u: 'A; v: 'B['u]; 'J['u, 'v] >- 'T['u, 'v] } -->
   sequent ['ext] { 'H; z: x:'A * 'B['x]; 'J['z] >- 'T['z] }

(*
 * H >- spread(e1; u1, v1. b1) = spread(e2; u2, v2. b2) in T[e1]
 * by spreadEquality (w:A * B)
 * H >- e1 = e2 in w:A * B
 * H, u:A, v: B[u], a: e1 = (u, v) in w:A * B >- b1[u; v] = b2[u; v] in T[u, v]
 *)
axiom spreadEquality 'H lambda{z. 'T['z]} (w:'A * 'B['w]) 'u 'v 'a :
   sequent [squash] { 'H >- 'e1 = 'e2 in w:'A * 'B['w] } -->
   sequent [squash] { 'H; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >-
             'b1['u; 'v] = 'b2['u; 'v] in 'T['u, 'v] } -->
   sequent ['ext] { 'H >- spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T['e1] }

(*
 * H >- a1:A1 * B1 <= a2:A2 * B2
 * by functionSubtype
 *
 * H >- A1 <= A2
 * H, a: A1 >- B1[a] <= B2[a]
 *)
axiom productSubtype 'H 'a :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { 'H >- subtype{ (a1:'A1 * 'B1['a1]); (a2:'A2 * 'B2['a2]) } }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_dprodT : int -> tactic
val eqcd_dprodT : tactic
val eqcd_pairT : tactic
val eqcd_spreadT : tactic

val dprod_term : term
val is_dprod_term : term -> bool
val dest_dprod : term -> string * term * term
val mk_dprod_term : string -> term -> term -> term

val prod_term : term
val is_prod_term : term -> bool
val dest_prod : term -> term * term
val mk_prod_term : term -> term -> term

val pair_term : term
val is_pair_term : term -> bool
val dest_pair : term -> term * term
val mk_pair_term : term -> term -> term

val spread_term : term
val is_spread_term : term -> bool
val dest_spread : term -> string * string * term * term
val mk_spread_term : string -> string -> term -> term -> term

(*
 * $Log$
 * Revision 1.7  1998/06/23 22:12:31  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 * Revision 1.6  1998/06/22 19:46:14  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.5  1998/06/15 22:33:16  jyh
 * Added CZF.
 *
 * Revision 1.4  1998/05/28 13:47:29  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.3  1998/04/22 22:44:42  jyh
 * *** empty log message ***
 *
 * Revision 1.2  1997/08/06 16:18:26  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:09  jyh
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
 * Revision 1.4  1996/09/02 19:37:20  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.3  1996/05/21 02:16:41  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:33:55  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/28 02:51:29  jyh
 * This is an initial version of the type theory.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
