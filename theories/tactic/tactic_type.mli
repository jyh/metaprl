(*
 * Define the common types.
 * A file with this name is required for every theory.
 *)

open Debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine

(*
 * Many tactics wish to examine their argument, so
 * the real type of tactic includes an argument.
 *)
type attribute =
   VarArgs of string list
 | TermArgs of term list
 | TypeArg of term
 | IntArgs of int list
 | ThinArg of bool
 | SubstArg of (string * term) list

(*
 * Every goal has a label.
 *)
type tactic_argument =
   { ref_label : string;
     ref_args : attribute list;
     ref_fcache : cache;
     ref_rsrc : tactic_resources
   }

and tactic_resources =
   { ref_d : int -> tactic;
     ref_eqcd : tactic;
     ref_typeinf : term_subst -> term -> term_subst * term;
     ref_squash : tactic;
     ref_subtype : tactic
   }

(*
 * A tactic takes these arguments.
 *)
and tactic_arg
and t
and tactic = tactic_arg -> t
and cache = tactic Tactic_cache.extract

(*
 * Two tactic_Arguments are equal.
 * Arguments are ignored, and only msequent part is compared.
 *)
val tactic_arg_alpha_equal : tactic_arg -> tactic_arg -> bool

(*
 * Projections.
 *)
val create_arg : msequent -> tactic_argument -> tactic_arg
val dest_arg   : tactic_arg -> msequent * tactic_argument
val tactic_seq : tactic_arg -> msequent
val tactic_arg : tactic_arg -> tactic_argument

(*
 * Apply a tactic.
 *)
val refine : tactic -> tactic_arg -> tactic_arg list * extract

(*
 * Convert prim forms into polymorphic forms.
 * This function is required by filter_prog.
 *)
val tactic_of_rule : prim_tactic -> address array * string array -> term list -> tactic

(*
 * Also convert rewrites.
 *)
val tactic_of_rewrite : rw -> tactic
val tactic_of_cond_rewrite : cond_rewrite -> tactic

(*
 * Basic tacticals.
 *)
val prefix_orelseT : tactic -> tactic -> tactic
val prefix_thenT : tactic -> tactic -> tactic
val prefix_thenLT : tactic -> tactic list -> tactic
val prefix_thenFLT : tactic -> (tactic_arg list -> t list) -> tactic

(*
 * $Log$
 * Revision 1.1  1998/06/03 22:20:02  jyh
 * Nonpolymorphic refiner.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
