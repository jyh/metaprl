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

open Itt_equal
open Itt_rfun
open Itt_struct

open Czf_itt_set

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare equiv{'s; 'r; 'a; 'b}
declare equiv{'s; 'r}
declare equiv_fun_set{'s; 'r; z. 'f['z]}
declare equiv_fun_prop{'s; 'r; z. 'P['z]}
(*declare equiv_dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]}*)

rewrite unfold_equiv : equiv{'s; 'r; 'a; 'b} <-->
   (((isset{'s} & isset{'r} & isset{'a} & isset{'b}) & mem{'a; 's} & mem{'b; 's}) & mem{pair{'a; 'b}; 'r})

rewrite unfold_equiv_fun_set : equiv_fun_set{'s; 'r; z. 'f['z]} <-->
   (all a: set. all b: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b} => equiv{'s; 'r; 'f['a]; 'f['b]}))

rewrite unfold_equiv_fun_prop : equiv_fun_prop{'s; 'r; z. 'P['z]} <-->
    (all a: set. all b: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b} => 'P['a] => 'P['b]))

(*rewrite unfold_equiv_dfun_prop : equiv_dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]} <-->
   (all s: set. all r: set. all a: set. all b: set. (equiv{'s; 'r; 'a; 'b} => (u1: 'A['a] -> 'B['a; 'u1] -> u2: 'A['b] -> 'B['b; 'u2])))
*)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_equiv_term : term -> bool
val mk_equiv_term : term -> term -> term -> term -> term
val dest_equiv : term -> term * term * term * term

val is_equiv_fun_set_term : term -> bool
val mk_equiv_fun_set_term : term -> term -> string -> term -> term
val dest_equiv_fun_set : term -> term * term * string * term

val is_equiv_fun_prop_term : term -> bool
val mk_equiv_fun_prop_term : term -> term -> string -> term -> term
val dest_equiv_fun_prop : term -> term * term * string * term

(*
 * Functionality.
 *)
topval equivFunSetT : int -> tactic
topval equivFunMemT : term -> int -> tactic

(*
 * Equivalence relations.
 *)
topval equivRefT : tactic
topval equivSymT : int -> tactic
topval equivTransT : term -> int -> tactic

(*
 * Substitution.
 *)
topval equivSubstT : term -> int -> tactic
