(*
 * Define the common types.
 *)

open Debug
open Refiner.Refiner
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
and tactic_arg = msequent * tactic_argument
and t = tactic_arg list * extract
and tactic = tactic_arg -> t
and cache = tactic Tactic_cache.extract

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Two args are equal.
 * Arguments are ignored.
 *)
let tactic_arg_alpha_equal (seq1, _) (seq2, _) =
   msequent_alpha_equal seq1 seq2

(*
 * Construction
 *)
let create_arg seq arg =
   seq, arg

let dest_arg seq_arg =
   seq_arg

let tactic_seq (seq, _) =
   seq

let tactic_arg (_, arg) =
   arg

(*
 * Refinement.
 *)
let refine tac arg =
   tac arg

(*
 * Construct polymorphic tactic.
 *)
let tactic_of_rule rule addrs_names params (seq, arg) =
   let rule = rule addrs_names params in
   let subgoals, ext = Refine.refine rule seq in
      List.map (fun seq -> seq, arg) subgoals, ext


(*
 * Convert a rewrite into a tactic.
 *)
let tactic_of_rewrite rw (seq, arg) =
   let rule = rwtactic rw in
   let subgoals, ext = Refine.refine rule seq in
      List.map (fun seq -> seq, arg) subgoals, ext

(*
 * Convert a conditional rewrite to a tactic.
 *)
let tactic_of_cond_rewrite crw (seq, arg) =
   let crw = crwtactic crw in
   let subgoals, ext = Refine.refine crw seq in
      List.map (fun seq -> seq, arg) subgoals, ext

(************************************************************************
 * TACTICALS                                                            *
 ************************************************************************)

(*
 * Flatten the subgoal list.
 *)
let rec flatten_subgoals = function
   (subgoals, ext) :: t ->
      let subgoals', extl = flatten_subgoals t in
         subgoals @ subgoals', ext :: extl
 | [] ->
      [], []

(*
 * Apply a tactic list to the goals.
 *)
let rec apply_subgoals = function
   (tac :: tacl), (subgoal :: subgoals) ->
      let subgoals', ext = refine tac subgoal in
      let subgoals'', extl = apply_subgoals (tacl, subgoals) in
         subgoals' @ subgoals'', ext :: extl
 | [], [] ->
      [], []
 | _ ->
      raise (RefineError (StringStringError ("thenLT", "length mismatch")))

(*
 * Sequencing tactics.
 *)
let prefix_orelseT tac1 tac2 goal =
   try tac1 goal with
      RefineError x ->
         try tac2 goal with
            RefineError y ->
               raise (RefineError (PairError ("orelseT", x, y)))

let prefix_thenT tac1 tac2 goal =
   let subgoals, ext = tac1 goal in
   let subgoals_ext = List.map tac2 subgoals in
   let subgoals', extl = flatten_subgoals subgoals_ext in
      subgoals', Refine.compose ext extl

let prefix_thenLT tac tacl goal =
   let subgoals, ext = tac goal in
   let subgoals, extl = apply_subgoals (tacl, subgoals) in
      subgoals, compose ext extl

let prefix_thenFLT tac1 tac2 goal =
   let subgoals, ext = tac1 goal in
   let subgoals_ext = tac2 subgoals in
   let subgoals, extl = flatten_subgoals subgoals_ext in
      subgoals, compose ext extl

(*
 * $Log$
 * Revision 1.1  1998/06/03 22:20:00  jyh
 * Nonpolymorphic refiner.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
