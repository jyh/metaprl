(*
 * Primitive axiomatization of implication.
 *)

include Czf_itt_and

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Implication is restricted.
 *)
axiom fun_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "fun"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
axiom fun_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "fun"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
axiom implies_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "implies"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
axiom implies_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "implies"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
axiom iff_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "iff"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
axiom iff_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "iff"{'A['x]; 'B['x]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
