(*
 * Primitive axiomatization of implication.
 *)

include Czf_itt_sep

open Refiner.Refiner.TermType

open Tacticals

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Implication is restricted.
axiom dfun_fun 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; v: set; z: 'A['v] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'A['z]} } -->
   sequent ['ext] { 'H; u: set; v: 'A['u] >- fun_prop{z. 'B['z; 'v]} } -->
   sequent ['ext] { 'H; u: set >- fun_prop{z. 'A['z]; w. 'B['u; 'w]} } -->
   sequent ['ext] { 'H >- fun_prop{z. "fun"{'A['z]; w. 'B['z; 'w]}} }

(*
 * Implication is restricted.
 *)
axiom prod_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "prod"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
axiom and_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "and"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
axiom and_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "and"{'A['x]; 'B['x]}} }
 *)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val type2T : tactic
val allAutoT : tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
