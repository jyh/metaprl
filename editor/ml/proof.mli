(*
 * A proof is a collection of inferences, where each inference is
 * a proof step or it is a nested proof.  Each inference
 * has the same goal as a subgoal of a previous inference.
 *
 *                   Goal           status:
 *                    |                bad: one if the proof_items has failed
 *                    |                partial: some incomplete subgoals
 *                    |                asserted: pretend like the proof is complete
 *                    |                complete: all steps have been checked
 *                    |
 *                   Item           proof_item
 *                  / | \
 *                 /  |  \
 *                /   |   \
 *               C1   C2  C3        children
 *              / |   |   | \
 *             /  |   |   |  \
 *            .   .   .   .   .
 *           .    .   .   .    .
 *          SG1  SG2 SG3 SG4  SG5   subgoals
 *
 * We also provide tools for navigation:
 *    1. Get the parent inference
 *    2. Get a subgoal inference
 *    3. Replace a subgoal inference
 *    4. Replace the tactic of the current inference
 *
 *)

open Term
open Refine

include Tactic_type

include Proof_step

(* Abstract type *)
type proof

(*
 * Head of a proof is a single step, or another proof.
 * This is the "justification" between the goal of the
 * proof and the first children.
 *)
type proof_item =
   ProofStep of Proof_step.t
 | ProofProof of proof

(*
 * Children are either leaves, or they
 * are subproofs.
 *)
type proof_child =
   ProofChildTerm of tactic_arg
 | ProofChildProof of proof

(*
 * Status of a proof node is cached,
 * but it can be computed from the children.
 * A proof is:
 *    bad: if the tactic in the rule box fails, or any of the children are bad
 *    partial: the proof is just a goal, or any of the children are partial
 *    asserted: force the proof to be accepted
 *    complete: all the children are complete
 *)
type proof_status =
   StatusBad
 | StatusPartial
 | StatusAsserted
 | StatusComplete

(*
 * An address is a integer path.
 *)
type address = int list

(*
 * This exception is raised when composed proofs don't match.
 * The goal if the subproof must be alpha-equal to the child
 * of the parent.
 *)
exception ProofMatch

(*
 * This exception is raised when a subgoal does
 * not exist at the given address.
 *)
exception InvalidAddress of proof * int

(*
 * Constructors
 *)
val proof_of_step : Proof_step.t -> proof

(*
 * Destructors of three types:
 * I. Proof as a whole
 *   a. proof_goal: main goal of the proof
 *   b. proof_subgoals: list the leaves of the proof
 * II. Uppermost inference only
 *   a. proof_item: first proof step
 *   b. proof_children: first list of nodes
 * III. Proof as subproof of a surrounding proof
 *   a. proof_parent: go up the tree one inference
 *   b. proof_main: get outermost proof
 *   c. proof_status: trace status of proof up the tree to root
 *   d. proof_address: return address of current proof relative to root
 *)
val proof_goal : proof -> tactic_arg
val proof_subgoals : proof -> tactic_arg list

val proof_item : proof -> proof_item
val proof_children : proof -> proof_child list

val proof_parent : proof -> proof option
val proof_main : proof -> proof
val proof_status : proof -> (proof_status * int) list
val proof_address : proof -> address

(*
 * Addressed subgoal.  The address is the
 * path to the subgoal -- raises InvalidAddress
 * if the address is bad.
 *)
val proof_index : proof -> address -> proof
val proof_child : proof -> int -> proof

(*
 * Functional updates.
 * For replace_item, the goal
 *    and subgoals must match the previous values.
 * For replace_child, the goal must match the given child goal.
 *)
val replace_item : proof -> proof_item -> proof
val replace_child : proof -> int -> proof -> proof
val remove_child : proof -> int -> proof
val remove_children : proof -> proof

(*
 * Check the proof and return its extract.
 * Two versions for handling refinement errors:
 *    check_proof: expand until first error, exceptions propagate
 *    expand_proof: check as much of the proof as possible,
 *       no exceptions are raised
 *)
val check_proof : refiner -> proof -> extract
val expand_proof : refiner -> proof -> unit

(*
 * IO
 *)
val io_proof_of_proof : proof -> Filter_proof_type.proof
val proof_of_io_proof : tactic_resources -> cache -> Filter_proof_type.proof -> proof

(*
 * $Log$
 * Revision 1.5  1998/04/22 14:06:23  jyh
 * Implementing proof editor.
 *
 * Revision 1.4  1998/04/17 01:30:46  jyh
 * Editor is almost constructed.
 *
 * Revision 1.3  1998/04/13 21:10:54  jyh
 * Added interactive proofs to filter.
 *
 * Revision 1.2  1998/04/09 19:07:25  jyh
 * Updating the editor.
 *
 * Revision 1.1  1997/08/06 16:17:22  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.4  1996/09/02 19:33:32  jyh
 * Semi-working package management.
 *
 * Revision 1.3  1996/05/21 02:25:38  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/05/20 17:00:07  jyh
 * This is an intermediate form of the editor with modules
 * before debugging.  Will be removing theoryGraph files next.
 *
 * Revision 1.1  1996/05/01 15:04:23  jyh
 * This is the initial checkin of the NuprlLight editor.  This editor provides
 * an emacs interface, a library navigator, and a proof editor.
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.top"
 * End:
 * -*-
 *)
