(*
 * We define a simple auto tactic, where it
 * is possible to add tactics to be tried by the auto tactic.
 *
 * This is the simple-minded auto tactic.  Each tactic
 * is given a precedence, and the tactics are ordered
 * by their precedences before they are tried.
 *
 * The trivialT tactic is like autoT, but it is intended
 * that trivialT either proves the goal or fails.
 *)

include Nltop

open Resource

open Tacticals
open Sequent

(*
 * This are the types.
 *)
type 'a auto_data
type auto_prec

(*
 * The info provided is a name,
 * a precedence, and a function
 * to produce a tactic.  The function
 * is called once per run of the auto tactic.
 *
 * One problem we have is that some tactics
 * may wish to keep some state.  The type system
 * won't allow us to make the struct polymorphic,
 * so we have the tactic produce a tactic
 * and a continuation.
 *)
type auto_tac =
   AutoTac of (tactic_arg -> (tactic * auto_tac) list)

type 'a auto_info =
   { auto_name : string;
     auto_prec : auto_prec;
     auto_tac : 'a
   }

(*
 * The string is for debugging.
 *)
resource (tactic auto_info, tactic, tactic auto_data) trivial_resource
resource (auto_tac auto_info, tactic, auto_tac auto_data) auto_resource

(*
 * Get values for the toploop.
 *)
val get_trivial_resource : string -> trivial_resource
val get_auto_resource : string -> auto_resource

(*
 * Operations on precedences.
 * The create operation takes a list of precedences that
 * are smaller, and another list that are larger.
 *)
val create_auto_prec : auto_prec list -> auto_prec list -> auto_prec

(*
 * It is also possible to remove a class of operations
 * by given their precedence.
 *)
val remove_auto_tactic :
   auto_resource ->
   auto_prec ->
   auto_resource

(*
 * Trivial is used by autoT.
 *)
val trivial_prec : auto_prec

(*
 * Trivial tactic.
 *)
topval trivialT : tactic

(*
 * The inherited tactic.
 *)
topval autoT : tactic

(*
 * These tactics are useful for trivial search.
 *)
topval onSomeHypT : (int -> tactic) -> tactic
topval onSomeAssumT : (int -> tactic) -> tactic

(*
 * Most times, a normal tactic is passed as auto_tac.
 * This wrapper converts it.
 *)
val auto_wrap : tactic -> auto_tac

(*
 * At other times, the search algorithm may want to
 * make sure the same configuration does not occur.
 * This wrapper will keep track of the sequents
 * seen, and fail if a sequent has been seen before.
 *)
val auto_progress : tactic -> auto_tac
val auto_hyp_progress : (int -> tactic_arg -> bool) -> (int -> tactic) -> auto_tac
val auto_assum_progress : (int -> tactic_arg -> bool) -> (int -> tactic) -> auto_tac

(*
 * $Log$
 * Revision 1.2  1998/07/21 22:45:04  jyh
 * Added NL toploop so that we can compile NL native code.
 *
 * Revision 1.1  1998/07/14 15:42:56  jyh
 * Intermediate version with auto tactic.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
