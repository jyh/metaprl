(*
 * This module defines some extra features _after_ equality
 * and subtyping have been defined.  This includes the "type"
 * judgement, and extensional type equality.
 *)

open Term

include Itt_equal
include Itt_subtype
include Itt_logic

(*
 * Terms type{'T} and subtype{'A; 'B} have already been defined.
 *)
rewrite type_def : "type"{'T} <--> subtype{'T; 'T}

define reduceExtEqual : ext_equal{'A; 'B} <--> subtype{'A; 'B} & subtype{'B; 'A}

(*
 * $Log$
 * Revision 1.1  1997/08/06 16:18:28  jyh
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
