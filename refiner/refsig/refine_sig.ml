(*
 * The refiner works on proof trees, which are trees of sequents.
 * A basic refinement takes a sequent (a "goal") and produces a
 * list of sequents (the "subgoals"), and an extract term.  The type
 * "tactic" packages refinements, and elements of tactics are
 * always "correct" in the sense that they can be reduced to steps
 * of primitive inferences.
 *
 * The refiner also tracks rewrites, and just as for tactics,
 * elements of type Rewrite are always "correct".
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *
 *)

open Opname

(************************************************************************
 * REFINER MODULE                                                       *
 ************************************************************************)

module type RefineSig =
sig
   type term
   type address
   type meta_term

   (*
    * Refinements are on meta-sequents,
    * which are a restricted form of meta terms,
    * having only dependent functions format.
    *
    * Each hyp is labelled by its first argument.
    *)
   type msequent

   (*
    * An ML rewrite replaces a term with another.
    *)
   type ml_extract = (string array * term list) -> term list -> term

   type ml_rewrite = term -> term

   type ml_cond_rewrite =
      string array ->                                   (* Names *)
         string list list ->                            (* Free vars in the msequent *)
         term list ->                                   (* Params *)
         term ->                                        (* Term to rewrite *)
         term * term list * string array * ml_extract   (* Extractor is returned *)

   (*
    * A condition relaces an goal with a list of subgoals,
    * and it provides a function to compute the extract.
    *)
   type ml_rule =
      address array ->                                  (* context addresses *)
         string array ->                                (* variable names *)
         msequent ->                                    (* goal *)
         term list ->                                   (* params *)
         msequent list * string array * ml_extract      (* subgoals, new variable names *)

   (************************************************************************
    * SENTINALS                                                            *
    ************************************************************************)

   (*
    * A checker is used to help make sure that the
    * refiner dependencies are respected.  However,
    * the real dependency checker checks the extract.
    *)
   type sentinal

   (*
    * Empty checker for just trying refinements.
    *)
   val any_sentinal : sentinal

   (*
    * Null sentinal allows no refinements.
    *)
   val null_sentinal : sentinal

   (************************************************************************
    * TACTICS                                                              *
    ************************************************************************)

   (*
    * An extract is an abstract validation that is generated during
    * proof refinement using tactics.
    *)
   type extract

   (*
    * A tactic is the reverse form of validation.
    * given a validation A -> B, that tactic would
    * prove B by asking for a subgoal A.
    *
    * Tactics operate on lists of terms.  These lists
    * represent meta-implications: the head term
    * is the goal, and the remainder are the assumptions.
    *)
   type tactic

   (* Tactic application *)
   val refine : sentinal -> tactic -> msequent -> msequent list * extract

   (* Proof composition *)
   val compose : extract -> extract list -> extract

   (* The base case tactic proves a goal by assumption *)
   val nth_hyp : int -> tactic

   (* The cut rule is primitive, but it doesn't weaken the logic *)
   val cut : term -> tactic

   (************************************************************************
    * REWRITES                                                             *
    ************************************************************************)

   (*
    * A rewrite extract is the validation for a rewrite.
    *)
   type rw_extract

   (*
    * A normal rewrite can be applied to a term to rewrite it.
    *)
   type rw_arg1 and rw_arg2 and rw_val
   type rw = rw_arg1 -> rw_arg2 -> rw_val

   (* Rewrite application *)
   val rw_refine : sentinal -> rw -> term -> term * rw_extract

   (* Rewrite composition *)
   val rw_compose : rw_extract -> address -> rw_extract -> rw_extract

   (* Reverse the rewrite *)
   val rw_reverse : rw_extract -> rw_extract

   (* Turn it into a regular extract *)
   val extract_of_rw_extract : msequent -> int -> rw_extract -> extract

   (*
    * Apply a rewrite to a subterm of the goal.
    *)
   val rwaddr : address -> rw -> rw

   (*
    * Apply the rewrite to the outermost where it does not fail.
    *)
   val rwhigher : rw -> rw

   (*
    * Convert a rewrite that likes to examine its argument.
    *)
   val rwtactic : int -> rw -> tactic

   (*
    * Composition is supplied for efficiency.
    *)
   val andthenrw : rw -> rw -> rw
   val orelserw : rw -> rw -> rw

   (************************************************************************
    * CONDITIONAL REWRITE                                                  *
    ************************************************************************)

   (*
    * A conditional rewrite validation.
    *)
   type crw_extract

   (*
    * A conditional rewrite is a cross between a rewrite and
    * a tactic.  An application may generate subgoals that must
    * be proved.  A conditional rewrite is valid only in a sequent
    * calculus.
    *)
   type crw_arg1 and crw_arg2 and crw_arg3 and crw_val
   type cond_rewrite = crw_arg1 -> crw_arg2 -> crw_arg3 -> crw_val

   (* Conditional rewrite application *)
   val crw_refine : sentinal -> cond_rewrite -> msequent -> term -> term * crw_extract

   (* Rewrite composition *)
   val crw_compose : crw_extract -> address -> crw_extract -> crw_extract

   (* Reverse the rewrite *)
   val crw_reverse : crw_extract -> crw_extract

   (* Turn it into a regular extract *)
   val extract_of_crw_extract : msequent -> int -> crw_extract -> extract

   (*
    * Ask for the current sequent, and for the term be rewritten.
    *)
   val crwaddr : address -> cond_rewrite -> cond_rewrite

   (*
    * Apply the rewrite to the outermost terms where it does not fail.
    *)
   val crwhigher : cond_rewrite -> cond_rewrite

   (*
    * Application of a conditional rewrite.
    * In this application, the rewrite must be applied to
    * a sequent, and it returns the rewritten sequent
    * as the first subgoal.
    *)
   val crwtactic : int -> cond_rewrite -> tactic

   (*
    * Composition is supplied for efficiency.
    *)
   val candthenrw : cond_rewrite -> cond_rewrite -> cond_rewrite
   val corelserw : cond_rewrite -> cond_rewrite -> cond_rewrite

   (************************************************************************
    * META SEQUENT                                                         *
    ************************************************************************)

   (*
    * Con/de-structors.
    *)
   val mk_msequent : term -> term list -> msequent
   val dest_msequent : msequent -> term * term list
   val msequent_goal : msequent -> term
   val msequent_num_assums : msequent -> int
   val msequent_nth_assum :  msequent -> int -> term
   val msequent_free_vars : msequent -> string list

   (*
    * Alpha equality on sequent objects.
    *)
   val msequent_alpha_equal : msequent -> msequent -> bool

   (*
    * Utils.
    *)
   val split_msequent_list : msequent list -> term list * term list list

   (************************************************************************
    * REFINER INTERFACE                                                    *
    ************************************************************************)

   (*
    * A refiner is basically just a collection of rules, tactics,
    * and rewrites.
    *)
   type refiner
   type build

   val null_refiner : string -> build
   val refiner_of_build : build -> refiner

   (*
    * These are the forms created at compile time with
    * extra arguments.
    *)
   type prim_tactic = address array * string array -> term list -> tactic
   type prim_rewrite = rw
   type prim_cond_rewrite = string array * term list -> cond_rewrite

   (*
    * Get the term corresponding to an extract.
    * This will fail if some of the rules are not justified
    * or if the extract is not complete.  The extract terms
    * for the arguments are included.
    *)
   val term_of_extract : refiner -> extract -> term list -> term

   (*
    * Get a checker from the refiner.
    *)
   val sentinal_of_refiner : refiner -> sentinal

   (*
    * An axiom is a term that is true.
    * This adds the theorem, and returns a tactic to prove a
    * goal that is the theorem.  This is used only in a sequent calculus.
    *
    * Once an axiom is defined, it can be justified as
    *    1. primitive (an term extract is given)
    *    2. derived (an extract from a proof is given)
    *    3. delayed (an extract can be computed on request)
    *)
   val create_axiom : build ->
      string ->                 (* name *)
      term ->                   (* statement *)
      prim_tactic
   val check_axiom : term -> unit
   val prim_axiom : build ->
      string ->                 (* name *)
      term ->                   (* extract *)
      unit
   val derived_axiom : build ->
      string ->                 (* name *)
      extract ->                (* derivation *)
      unit
   val delayed_axiom : build ->
      string ->                 (* name *)
      (unit -> extract) ->      (* derivation *)
      unit

   (*
    * A rule is an implication on terms (the conclusion
    * is true if all the antecedents are).
    *     Args: refiner, name, addrs, params, rule
    *)
   val create_rule : build ->
      string ->            (* name *)
      string array ->      (* addrs *)
      string array ->      (* vars *)
      term list ->         (* params *)
      meta_term ->         (* rule definition *)
      prim_tactic
   val create_ml_rule : build -> string ->
      ml_rule ->                 (* the rule definition *)
      prim_tactic
   val check_rule :
      string ->            (* name *)
      string array ->      (* addrs *)
      string array ->      (* vars *)
      term list ->         (* params *)
      meta_term ->         (* rule definition *)
      unit

   val prim_rule : build ->
      string ->                    (* name *)
      string array ->              (* vars *)
      term list ->                 (* params *)
      term list ->                 (* args (binding vars) *)
      term ->                      (* extract *)
      unit
   val derived_rule : build ->
      string ->                    (* name *)
      string array ->              (* vars *)
      term list ->                 (* params *)
      term list ->                 (* args (binding vars) *)
      extract ->                   (* derived justification *)
      unit
   val delayed_rule : build ->
      string ->                    (* name *)
      string array ->              (* vars *)
      term list ->                 (* params *)
      term list ->                 (* args (binding vars) *)
      (unit -> extract) ->         (* derived justification *)
      unit

   (*
    * Rewrites.
    *)
   val create_rewrite : build ->
      string ->            (* name *)
      term ->              (* redex *)
      term ->              (* contractum *)
      prim_rewrite
   val create_input_form : build ->
      string ->            (* name *)
      bool ->              (* relaxed/strict *)
      term ->              (* redex *)
      term ->              (* contractum *)
      prim_rewrite
   val create_ml_rewrite : build -> string ->
      ml_rewrite ->        (* rewriter *)
      prim_rewrite
   val prim_rewrite : build ->
      string ->            (* name *)
      term ->              (* redex *)
      term ->              (* contractum *)
      unit
   val derived_rewrite : build ->
      string ->            (* name *)
      term ->              (* redex *)
      term ->              (* contractum *)
      extract ->           (* proof *)
      unit
   val delayed_rewrite : build ->
      string ->            (* name *)
      term ->              (* redex *)
      term ->              (* contractum *)
      (unit -> extract) -> (* proof *)
      unit

   val create_cond_rewrite : build ->
      string ->            (* name *)
      string array ->      (* vars *)
      term list ->         (* params *)
      term list ->         (* subgoals *)
      term ->              (* redex *)
      term ->              (* contractum *)
      prim_cond_rewrite
   val create_ml_cond_rewrite : build -> string ->
      ml_cond_rewrite ->   (* rewriter *)
      prim_cond_rewrite
   val prim_cond_rewrite : build ->
      string ->            (* name *)
      string array ->      (* vars *)
      term list ->         (* params *)
      term list ->         (* subgoals *)
      term ->              (* redex *)
      term ->              (* contractum *)
      unit
   val derived_cond_rewrite : build ->
      string ->            (* name *)
      string array ->      (* vars *)
      term list ->         (* params *)
      term list ->         (* subgoals *)
      term ->              (* redex *)
      term ->              (* contractum *)
      extract ->           (* proof *)
      unit
   val delayed_cond_rewrite : build ->
      string ->            (* name *)
      string array ->      (* vars *)
      term list ->         (* params *)
      term list ->         (* subgoals *)
      term ->              (* redex *)
      term ->              (* contractum *)
      (unit -> extract) -> (* proof *)
      unit
   val check_rewrite :
      string ->            (* string *)
      string array ->      (* vars *)
      term list ->         (* params *)
      term list ->         (* subgoals *)
      term ->              (* redex *)
      term ->              (* contractum *)
      unit

   (*
    * Merge refiners.
    *)
   val label_refiner : build -> string -> refiner
   val join_refiner : build -> refiner -> unit

   (************************************************************************
    * DESTRUCTION                                                          *
    ************************************************************************)

   (*
    * Destruct extracts.
    * the guarantee is that extracts, when destructed and composed, will
    * be equal.
    *)
   type atomic_just =
      { just_goal : msequent;
        just_addrs : address array;
        just_names : string array;
        just_params : term list;
        just_refiner : opname;
        just_subgoals : msequent list
      }

   type cut_just =
      { cut_goal : msequent;
        cut_hyp : term;
        cut_lemma : msequent;
        cut_then : msequent
      }

   type extract_info =
      AtomicExtract of atomic_just
    | RewriteExtract of msequent * rw_extract * msequent
    | CondRewriteExtract of msequent * crw_extract * msequent list
    | ComposeExtract of extract * extract list
    | NthHypExtract of msequent * int
    | CutExtract of cut_just

   type rw_extract_info =
      AtomicRewriteExtract of term * opname * term
    | ReverseRewriteExtract of rw_extract
    | ComposeRewriteExtract of rw_extract * rw_extract
    | AddressRewriteExtract of term * address * rw_extract * term
    | HigherRewriteExtract of term * rw_extract list * term

   type cond_rewrite_here =
      { cjust_goal : term;
        cjust_names : string array;
        cjust_params : term list;
        cjust_refiner : opname;
        cjust_subgoal_term : term;
        cjust_subgoals : term list
      }

   type crw_extract_info =
      AtomicCondRewriteExtract of cond_rewrite_here
    | ReverseCondRewriteExtract of crw_extract
    | ComposeCondRewriteExtract of crw_extract * crw_extract
    | AddressCondRewriteExtract of term * address * crw_extract * term
    | HigherCondRewriteExtract of term * crw_extract list * term

   val dest_extract : extract -> extract_info
   val goal_of_extract : extract -> msequent
   val subgoals_of_extract : extract -> msequent list

   val dest_rw_extract : rw_extract -> rw_extract_info
   val goal_of_rw_extract : rw_extract -> term
   val subgoal_of_rw_extract : rw_extract -> term

   val dest_crw_extract : crw_extract -> crw_extract_info
   val goal_of_crw_extract : crw_extract -> term
   val subgoal_of_crw_extract : crw_extract -> term
   val subgoals_of_crw_extract : crw_extract -> (address * term) list

   (*
    * Describe the contents of the refiner.
    *)
   type refiner_item =
      RIAxiom of ri_axiom
    | RIRule of ri_rule
    | RIPrimTheorem of ri_prim_theorem
    | RIMLRule of ri_ml_rule

    | RIRewrite of ri_rewrite
    | RIMLRewrite of ri_ml_rewrite
    | RICondRewrite of ri_cond_rewrite
    | RIPrimRewrite of ri_prim_rewrite
    | RIMLCondRewrite of ri_ml_rewrite

    | RIParent of refiner
    | RILabel of string

   and ri_axiom =
      { ri_axiom_name : opname;
        ri_axiom_term : term
      }
   and ri_rule =
      { ri_rule_name : opname;
        ri_rule_rule : msequent
      }
   and ri_ml_rule =
      { ri_ml_rule_name : opname }
   and ri_prim_theorem =
      { ri_pthm_axiom : refiner }

   and ri_rewrite =
      { ri_rw_name : opname;
        ri_rw_redex : term;
        ri_rw_contractum : term
      }
   and ri_cond_rewrite =
      { ri_crw_name : opname;
        ri_crw_conds : term list;
        ri_crw_redex : term;
        ri_crw_contractum : term
      }
   and ri_prim_rewrite =
      { ri_prw_rewrite : refiner }
   and ri_ml_rewrite =
      { ri_ml_rw_name : opname }

   (*
    * Destructors.
    * dest_refiner raises (Invalid_argument "dest_refiner") if the refiner is empty
    *)
   val is_null_refiner : refiner -> bool
   val dest_refiner : refiner -> refiner_item * refiner
   val find_refiner : refiner -> opname -> refiner
end

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner.run"
 * End:
 * -*-
 *)
