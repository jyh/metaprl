(*
 * This is the TPTP tactic to prove TPTP goals.
 *)

open Refiner.Refiner.TermType
open Refiner.Refiner.TermSubst

open Tacticals

topval resolveT : int -> tactic
topval proveT : tactic

topval testT : tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
