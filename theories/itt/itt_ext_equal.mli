(*
 * This module defines some extra features _after_ equality
 * and subtyping have been defined.  This includes the "type"
 * judgement, and extensional type equality.
 *)

open Refiner.Refiner.Term

include Itt_equal
include Itt_subtype
include Itt_logic

(*
 * Terms type{'T} and subtype{'A; 'B} have already been defined.
 *)
rewrite type_def : "type"{'T} <--> subtype{'T; 'T}

define unfoldExtEqual : ext_equal{'A; 'B} <--> subtype{'A; 'B} & subtype{'B; 'A}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
