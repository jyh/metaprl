(*
 * Boolean operations.
 *)

include Itt_equal

open Refiner.Refiner.Term
open Tactic_type

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "bool"

declare "btrue"
declare "bfalse"
declare bor{'a; 'b}
declare band{'a; 'b}
declare bnot{'a; 'b}

declare ifthenelse{'e1; 'e2; 'e3}

(*
 * This term is used to reduce param actions.
 *)
declare "bool_flag"[@n:t]

rewrite boolTrue : "bool_flag"["true":t] <--> "btrue"
rewrite boolFalse : "bool_flag"["false":t] <--> "bfalse"

(*
 * Reduction.
 *)
rewrite ifthenelseTrue : ifthenelse{btrue; 'e1; 'e2} <--> 'e1
rewrite ifthenelseFalse : ifthenelse{bfalse; 'e1; 'e2} <--> 'e2
rewrite reduceBor : bor{'a; 'b} <--> ifthenelse{'a; btrue; 'b}
rewrite reduceBand : band{'a; 'b} <--> ifthenelse{'a; 'b; bfalse}
rewrite reduceBnot : bnot{'a} <--> ifthenelse{'a; bfalse; btrue}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Unit
 * by boolFormation
 *)
axiom boolFormation 'H : sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- Bool = Bool in Ui ext Ax
 * by boolEquality
 *)
axiom boolEquality 'H : sequent ['ext] { 'H >- "bool" = "bool" in univ[@i:l] }

(*
 * H >- Bool ext btrue
 * by bool_*Formation
 *)
axiom bool_trueFormation 'H : sequent ['ext] { 'H >- "bool" }
axiom bool_falseFormation 'H : sequent ['ext] { 'H >- "bool" }

(*
 * H >- Unit = Unit in Ui ext Ax
 * by boolEquality
 *)
axiom bool_trueEquality 'H : sequent ['ext] { 'H >- btrue = btrue in "bool" }
axiom bool_falseEquality 'H : sequent ['ext] { 'H >- bfalse = bfalse in "bool" }

(*
 * H; i:x:Unit; J >- C
 * by boolElimination i
 * H; i:x:Unit; J[it / x] >- C[it / x]
 *)
axiom boolElimination 'H 'J 'x :
   sequent['ext] { 'H; x: "bool"; 'J[btrue] >- 'C[btrue] } -->
   sequent['ext] { 'H; x: "bool"; 'J[bfalse] >- 'C[bfalse] } -->
   sequent ['ext] { 'H; x: "bool"; 'J['x] >- 'C['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_boolT : int -> tactic
val eqcd_boolT : tactic
val eqcd_btrueT : tactic
val eqcd_bfalseT : tactic
val bool_term : term
val btrue_term : term
val bfalse_term : term

(*
 * $Log$
 * Revision 1.2  1998/06/12 18:36:36  jyh
 * Working factorial proof.
 *
 * Revision 1.1  1998/06/12 13:47:22  jyh
 * D tactic works, added itt_bool.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
