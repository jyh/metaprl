(*
 * Primitive axiomatization of implication.
 *)

include Czf_itt_sep

open Refiner.Refiner.TermType

open Tacticals

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

axiom dprod_fun3 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'A['z]} } -->
   sequent ['ext] { 'H >- dfun_prop{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- fun_prop{z. "prod"{'A['z]; w. 'B['z; 'w]}} }

axiom dprod_res3 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- restricted{z. "prod"{'A['z]; w. 'B['z; 'w]}} }

axiom exists_fun 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'A['z]} } -->
   sequent ['ext] { 'H >- dfun_prop{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- fun_prop{z. "exists"{'A['z]; w. 'B['z; 'w]}} }

axiom exists_res 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- restricted{z. "exists"{'A['z]; w. 'B['z; 'w]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
