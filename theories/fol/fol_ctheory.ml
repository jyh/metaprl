(*
 * Constructive logic.
 *)

extends Fol_type
extends Fol_true
extends Fol_false
extends Fol_implies
extends Fol_and
extends Fol_or
extends Fol_not
extends Fol_univ
extends Fol_all
extends Fol_exists
extends Fol_struct

open Fol_implies
open Fol_and
open Fol_or
open Fol_not
open Fol_all
open Fol_exists

prec prec_implies < prec_and
prec prec_implies < prec_or
prec prec_or < prec_and
prec prec_and < prec_not
prec prec_all < prec_implies
prec prec_exists < prec_implies

interactive or_choice :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{'C} } -->
   sequent ['ext] { 'H >- (('A or 'B) => 'C) => 'A => 'C }

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
