(*
 * Constructive logic.
 *)

include Fol_type
include Fol_true
include Fol_false
include Fol_implies
include Fol_and
include Fol_or
include Fol_not
include Fol_univ
include Fol_all
include Fol_exists
include Fol_struct

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

interactive or_choice 'H :
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
