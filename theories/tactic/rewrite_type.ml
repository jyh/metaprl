(*
 * This is the basic rewrite data type.
 * A file with this name is required for every theory.
 *)

open Refiner.Refiner
open Refiner.Refiner.Refine
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermAddr

open Tactic_type
open Tacticals

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * A conversion is wither a regular rewrite,
 * or a conditional rewrite, or a composition.
 *)
type t = tactic

and env = tactic_arg * address

and conv = env -> t

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Get the term of the environment.
 *)
let env_term (arg, addr) =
   term_subterm (Sequent.goal arg) addr

(*
 * Get the sequent that we are matching against.
 *)
let env_goal (arg, _) =
   Sequent.goal arg

(*
 * Create a conversion from a basic rewrite.
 * This function is required by filter_prog.
 *)
let rewrite_of_rewrite rw (_, addr) =
   tactic_of_rewrite (rwaddr addr rw)

(*
 * Create a conversion from a conditional rewrite.
 * This function is required by filter_prog.
 *)
let rewrite_of_cond_rewrite crw args (_, addr) =
   tactic_of_cond_rewrite (crwaddr addr (crw args))

(*
 * Composition.
 *)
let prefix_andthenC conv1 conv2 (_, addr) =
   let tac1 p = conv1 (p, addr) p in
   let tac2 p = conv2 (p, addr) p in
      tac1 thenT tac2

let prefix_orelseC conv1 conv2 (_, addr) =
   let tac1 p = conv1 (p, addr) p in
   let tac2 p = conv2 (p, addr) p in
      tac1 orelseT tac2

(*
 * No action.
 *)
let idC _ =
   idT

(*
 * Apply the conversion at the specified address.
 *)
let addrC addr conv (_, addr') =
   let addr = make_address addr in
   let addr = compose_address addr' addr in
      (fun p -> conv (p, addr) p)

(*
 * Apply the rewrite.
 *)
let rw conv i p =
   let addr = Sequent.clause_addr p i in
      conv (p, addr) p

(*
 * $Log$
 * Revision 1.1  1998/06/03 22:19:55  jyh
 * Nonpolymorphic refiner.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
