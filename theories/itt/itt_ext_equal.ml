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
 * $Log$
 * Revision 1.4  1998/06/15 22:33:19  jyh
 * Added CZF.
 *
 * Revision 1.3  1998/05/28 13:47:33  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.2  1998/04/24 02:43:27  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.1  1997/08/06 16:18:27  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
