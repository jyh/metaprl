(*
 * Lists.
 *
 *)

open Term

include Tactic_type

include Itt_equal
include Itt_rfun

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare nil
declare cons{'a; 'b}

declare list{'a}
declare list_ind{'e; 'base; h, t, f. 'step['h; 't; 'f]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Reduction.
 *)
rewrite list_indReduceBase :
   list_ind{nil; 'base; h, t, f. 'step['h; 't; 'f]} <--> 'base

rewrite list_indReduceStep :
   list_ind{('u :: 'v); 'base; h, t, f. 'step['h; 't; 'f]} <-->
      'step['u; 'v; list_ind{'v; 'base; h, t, f. 'step['h; 't; 'f]}]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext list(A)
 * by listFormation
 *
 * H >- Ui ext A
 *)
axiom listFormation 'H :
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- list(A) = list(B) in Ui
 * by listEquality
 *
 * H >- A = B in Ui
 *)
axiom listEquality 'H :
   sequent [squash] { 'H >- 'A = 'B in univ[@i:l] } -->
   sequent ['ext] { 'H >- list{'A} = list{'B} in univ[@i:l] }

(*
 * H >- list(A) ext nil
 * by nilFormation
 *
 * H >- A = A in Ui
 *)
axiom nilFormation 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- 'A list }

(*
 * H >- nil = nil in list(A)
 * by nilEquality
 *
 * H >- A = A in Ui
 *)
axiom nilEquality 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- nil = nil in list{'A} }

(*
 * H >- list(A) ext cons(h; t)
 * by consFormation
 *
 * H >- A ext h
 * H >- list(A) ext t
 *)
axiom consFormation 'H :
   sequent ['ext] { 'H >- 'A } -->
   sequent ['ext] { 'H >- list{'A} } -->
   sequent ['ext] { 'H >- list{'A} }

(*
 * H >- u1::v1 = u2::v2 in list(A)
 * consEquality
 *
 * H >- u1 = u2 in A
 * H >- v1 = v2 in list(A)
 *)
axiom consEquality 'H :
   sequent [squash] { 'H >- 'u1 = 'u2 in 'A } -->
   sequent [squash] { 'H >- 'v1 = 'v2 in list{'A} } -->
   sequent ['ext] { 'H >- cons{'u1; 'v1} = cons{'u2; 'v2} in list{'A} };;

(*
 * H; l: list(A); J[l] >- C[l]
 * by listElimination w u v
 *
 * H; l: list(A); J[l] >- C[nil]
 * H; l: list(A); J[l]; u: A; v: list(A); w: C[v] >- C[u::v]
 *)
axiom listElimination 'H 'J 'l 'w 'u 'v :
   sequent ['ext] { 'H; l: list{'A}; 'J['l] >- 'C[nil] } -->
   sequent ['ext] { 'H; l: list{'A}; 'J['l]; u: 'A; v: list{'A}; w: 'C['v] >- 'C['u::'v] } -->
   sequent ['ext] { 'H; l: list{'A}; 'J['l] >- 'C['l] }

(*
 * H >- rec_case(e1; base1; u1, v1, z1. step1[u1; v1]
 *      = rec_case(e2; base2; u2, v2, z2. step2[u2; v2]
 *      in T[e1]
 *
 * by list_indEquality lambda(r. T[r]) list(A) u v w
 *
 * H >- e1 = e2 in list(A)
 * H >- base1 = base2 in T[nil]
 * H, u: A; v: list(A); w: T[v] >- step1[u; v; w] = step2[u; v; w] in T[u::v]
 *)
axiom list_indEquality 'H lambda{l. 'T['l]} list{'A} 'u 'v 'w :
   sequent [squash] { 'H >- 'e1 = 'e2 in list{'A} } -->
   sequent [squash] { 'H >- 'base1 = 'base2 in 'T[nil] } -->
   sequent [squash] { 'H; u: 'A; v: list{'A}; w: 'T['v] >-
             'step1['u; 'v; 'w] = 'step2['u; 'v; 'w] in 'T['u::'v]
           } -->
   sequent ['ext] { 'H >- list_ind{'e1; 'base1; u1, v1, z1. 'step1['u1; 'v1; 'z1]}
                   = list_ind{'e2; 'base2; u2, v2, z2. 'step2['u2; 'v2; 'z2]}
                   in 'T['e1]
           }
   
(*
 * H >- list(A1) <= list(A2)
 * by listSubtype
 *
 * H >- A1 <= A2
 *)
axiom listSubtype 'H :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent ['ext] { 'H >- subtype{list{'A1}; list{'A2}}}

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_listT : int -> tactic
val eqcd_listT : tactic

val list_term : term
val is_list_term : term -> bool
val dest_list : term -> term
val mk_list_term : term -> term

val nil_term : term

val is_cons_term : term -> bool
val dest_cons : term -> term * term
val mk_cons_term : term -> term -> term

val is_list_ind_term : term -> bool
val dest_list_ind : term -> term * term * string * string * string * term
val mk_list_ind_term : term -> term -> string -> string -> string -> term -> term

(*
 * $Log$
 * Revision 1.2  1997/08/06 16:18:34  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:17  jyh
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
 * Revision 1.4  1996/09/02 19:37:28  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.3  1996/05/21 02:16:56  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:05  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/30 01:37:15  jyh
 * Initial version of ITT.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
