(*
 * This module defines some extra features _after_ equality
 * and subtyping have been defined.  This includes the "type"
 * judgement, and extensional type equality.
 *)

open Printf
open Debug
open Refiner.Refiner.Term

include Itt_equal
include Itt_squash
include Itt_subtype
include Itt_logic

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_ext_equal%t" eflush

(*
 * Terms type{'T} and subtype{'A; 'B} have already been defined.
 *)
primrw type_def : "type"{'T} <--> subtype{'T; 'T}

declare ext_equal{'A; 'B}
primrw unfoldExtEqual : ext_equal{'A; 'B} <--> subtype{'A; 'B} & subtype{'B; 'A}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
