(*!
 * @spelling{arg tac}
 *
 * @begin[doc]
 * @theory[Base_auto_tactic]
 *
 * The @tt{Base_auto_tactic} module defines two of the most useful
 * tactics in the @MetaPRL prover.  The @tactic[autoT] tactic attempts
 * to prove a goal ``automatically,'' and the @tactic[trivialT] tactic
 * proves goals that are ``trivial.''  Their implementations are surprisingly
 * simple---all of the work in automatic proving is implemented in
 * descendent theories.
 *
 * This module describes the @emph{generic} implementation of the
 * @hreftactic[autoT] and @hreftactic[trivialT] tactics.  They are implemented as resources
 * containing collections of tactics that are added by descendent theories.
 * The @Comment!resource[auto_resource] builds collections of tactics specified by
 * a data structure with the following type:
 *
 * @begin[center]
 * @begin[verbatim]
 * type auto_tac = tactic_arg -> (tactic * auto_tac) list
 *
 * type auto_info =
 *    { auto_name : string;
 *      auto_prec : auto_prec;
 *      auto_tac : auto_tac
 *    }
 * @end[verbatim]
 * @end[center]
 *
 * The @tt{auto_name} is the name used to describe the entry (for
 * debugging purposes).  The @tt{auto_tac} is a function that takes
 * the current goal (the @tt{tactic_arg}) and provides a tactic that
 * can be applied to the goal, and a new @tt{auto_tac} that can be
 * used on the subgoals.  The entries are divided into precedence
 * levels; tactics with higher precedence are applied first.
 *
 * In most cases, the @tt{auto_tac} is a simple function that
 * just applies a tactic repeatedly.  The following function
 * converts a simple tactic into an @tt{auto_tac}.
 *
 * @begin[center]
 * @begin[verbatim]
 * let rec auto_wrap (tac : tactic) =
 *    (fun p -> [tac, auto_wrap tac])
 * @end[verbatim]
 * @end[center]
 *
 * The more general form of @tt{auto_tac} (where a new tactic is
 * computed for each goal) is used for tactics that keep track of
 * their context.  For instance, a first-order prover may wish to keep
 * a cache of goals that have been examined, and avoid proving the same
 * goal multiple times.
 *
 * The @hreftactic[trivialT] is similar to the @hreftactic[autoT] tactic; it uses the same
 * data structures, but it is used to classify only ``trivial'' tactics (such
 * as proof by assumption).  The separation is made for practical purposes.
 * At times, the @hreftactic[autoT] tactic may spend significant time performing
 * sophisticated reasoning when a goal has a trivial proof.  The @hreftactic[trivialT]
 * is added to the @hrefresource[auto_resource] with a high precedence, so ``trivial''
 * reasoning is included by default in @hreftactic[autoT].
 *
 * This theory also defines the @tactic[byDefT] tactic. @tt{byDefT }@i{conv}
 * (where @i{conv} is usially an @tt{unfold_} conversional) uses @i{conv}
 * (through @hreftactic[higherC]) on all the assumptions and on the goal and then
 * calls @hreftactic[autoT].
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * @email{jyh@cs.caltech.edu}
 *
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Mptop
(*! @docoff *)

open Printf
open Mp_debug
open Dag
open Imp_dag

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Top_conversionals
open Mptop

(*
 * Debugging.
 *)
let _ =
   show_loading "Loading Base_auto_tactic%t"

let debug_auto =
   create_debug (**)
      { debug_name = "auto";
        debug_description = "Display auto tactic operations";
        debug_value = false
      }

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * The auto tactic just produces a list of tactics to try.
 *)
type auto_prec = unit ImpDag.node

(*
 * The info provided is a name,
 * a precedence, and a function
 * to produce a tactic.  The function
 * is called once per run of the auto tactic.
 *)
type auto_tac =
   AutoTac of (tactic_arg -> (tactic * auto_tac) list)

type 'a auto_info =
   { auto_name : string;
     auto_prec : auto_prec;
     auto_tac : 'a
   }

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * We create a DAG to manage ordering in the tree.
 *)
let dag = ImpDag.create ()

(*
 * See if a prec is in a list of precs.
 *)
let rec node_member node = function
   node' :: nodes ->
      if ImpDag.node_rel dag node node' = Equal then
         true
      else
         node_member node nodes
 | [] ->
      false

(*
 * Sort the nodes in the list.
 *)
let sort_nodes nodes =
   let compare { auto_prec = node1 } { auto_prec = node2 } =
      ImpDag.node_rel dag node1 node2 = LessThan
   in
      Sort.list compare nodes

(*
 * Debugging firstT.
 *)
let rec firstDebugT tacs p =
   match tacs with
      [{ auto_name = name; auto_tac = tac}] ->
         eprintf "firstDebugT: trying %s%t" name eflush;
         tac p
    | ({ auto_name = name; auto_tac = tac } :: tacs) ->
         eprintf "firstDebugT: trying %s%t" name eflush;
         (tac orelseT firstDebugT tacs) p
    | [] ->
         eprintf "firstDebugT: failed%t" eflush;
         raise (RefineError ("firstDebugT", StringError "no tactics"))

(*
 * Compute the tactic to be tried.
 *)
let compileSimpleT tacs p =
   firstT (List.map (fun tac -> tac.auto_tac) tacs) p

let compileDebugT tacs p =
   firstDebugT tacs p

let compileTrivialT tacs p =
   if !debug_auto then
      compileDebugT tacs p
   else
      compileSimpleT tacs p

(*
 * Auto tactic performs a repeat.
 *)
let rec compileDebugAutoT tacs p =
   eprintf "Starting new auto trial%t" eflush;
   let v = loopDebugT 0 tacs tacs p in
      eprintf "Finished auto trial%t" eflush;
      v

and loopDebugT i tacs tacs' p =
   match tacs' with
      (name,  AutoTac tac) :: tacs' ->
         eprintf "Trying %s%t" name eflush;
         let rec chooseT = function
            (tac, cont) :: tacs'' ->
               eprintf "\tTrying %s%t" name eflush;
               ((tac thenT (fun p -> compileDebugAutoT (List_util.replace_nth i (name, cont) tacs) p))
                orelseT chooseT tacs'')
          | [] ->
               loopDebugT (i + 1) tacs tacs'
         in
            chooseT (tac p) p
    | [] ->
         eprintf "All tactics failed%t" eflush;
         idT p

let rec compileSimpleAutoT tacs p =
   loopSimpleT 0 tacs tacs p

and loopSimpleT i tacs tacs' p =
   match tacs' with
      AutoTac tac :: tacs' ->
         let rec chooseT = function
            (tac, cont) :: tacs'' ->
               ((tac thenT (fun p -> compileSimpleAutoT (List_util.replace_nth i cont tacs) p))
                orelseT chooseT tacs'')
          | [] ->
               loopSimpleT (i + 1) tacs tacs'
         in
            chooseT (tac p) p
    | [] ->
         idT p

let compileAutoT tacs p =
   if !debug_auto then
      compileDebugAutoT (List.map (fun { auto_name = name; auto_tac = tac } -> name, tac) tacs) p
   else
      compileSimpleAutoT (List.map (fun item -> item.auto_tac) tacs) p

(*
 * Build an auto tactic from all of the tactics given.
 * A list of tactics to try is constructed.
 * The earlier tactics should be tried first.
 *)
let extract compile tactics =
   let tactics = sort_nodes tactics in
      if !debug_auto then
         begin
            eprintf "Auto tactics:%t" eflush;
            List.iter (fun { auto_name = name } -> eprintf "\t%s%t" name eflush) tactics
         end;
      compile tactics

(*
 * Wrap a regular tactic.
 *)
let rec auto_wrap (tac : tactic) =
   AutoTac (fun p -> [tac, auto_wrap tac])

let improve_resource data info = info::data

let make_auto_tactic name context_args var_args term_args pre_tactic =
   match context_args, term_args with
      [| _ |], [] ->
         (fun p ->
               let vars = Var.maybe_new_vars_array p var_args in
               let addr = hyp_count_addr p in
                  Tactic_type.Tactic.tactic_of_rule pre_tactic ([| addr |], vars) [] p)
    | _, [] ->
         raise (Invalid_argument (sprintf "Base_auto_tactic.improve: %s: only introduction rules are allowed" name))
    | _ ->
         raise (Invalid_argument (sprintf "Base_auto_tactic.improve: %s: term arguments are not allowed in auto tactics" name))

let process_trivial_resource_annotation name context_args var_args term_args _ _ (pre_tactic, tprec) =
   let tac = make_auto_tactic name context_args var_args term_args pre_tactic in
      { auto_name = name; auto_prec = tprec; auto_tac = tac }

let process_auto_resource_annotation name context_args var_args term_args _ _ (pre_tactic, tprec) =
   let tac = make_auto_tactic name context_args var_args term_args pre_tactic in
      { auto_name = name; auto_prec = tprec; auto_tac = auto_wrap tac }

(*
 * Resource.
 *)
let resource trivial = Functional {
   fp_empty = [];
   fp_add = improve_resource;
   fp_retr = extract compileTrivialT
}

let resource auto = Functional {
   fp_empty = [];
   fp_add = improve_resource;
   fp_retr = extract compileAutoT
}

(*
 * Create a precedence.
 *)
let create_auto_prec before after =
   let node = ImpDag.insert dag () in
      List.iter (fun p -> ImpDag.add_edge dag p node) before;
      List.iter (fun p -> ImpDag.add_edge dag node p) after;
      node

(*
 * Use the tactic as long as progress is being made.
 *)
let rec check_progress goal = function
   goal' :: goals ->
      if alpha_equal goal goal' then
         true
      else
         check_progress goal goals
 | [] ->
      false

let rec try_progressT goals tac p =
   let goal = Sequent.goal p in
      if check_progress goal goals then
         [] (* raise (RefineError ("auto_progress", StringError "no progress")) *)
      else
         [tac, AutoTac (fun p -> try_progressT (goal :: goals) tac p)]

let auto_progress (tac : tactic) =
   AutoTac (fun p -> try_progressT [] tac p)

(*
 * Progress on some hyp.
 * This is a little more general because multiple hyps can be tried.
 *)
let rec check_hyp_progress i goal = function
   (i', goal') :: goals ->
      if i = i' & alpha_equal goal goal' then
         true
      else
         check_hyp_progress i goal goals
 | [] ->
      false

let rec try_hyp_progressT test hyps tac p =
   let rec expand hyps' i len =
      if i > len then
         []
      else
         match SeqHyp.get hyps' (i - 1) with
            Hypothesis (_, hyp)  ->
               if not (test i p) or check_hyp_progress i hyp hyps then
                  expand hyps' (i + 1) len
               else
                  let item = tac i, AutoTac (try_hyp_progressT test ((i, hyp) :: hyps) tac) in
                     item :: expand hyps' (i + 1) len
          | Context _ ->
               expand hyps' (i + 1) len
   in
   let { sequent_hyps = hyps } = Sequent.explode_sequent p in
      expand hyps 1 (SeqHyp.length hyps)

let auto_hyp_progress test (tac : int -> tactic) =
   AutoTac (try_hyp_progressT test [] tac)

(*
 * Progress on assumptions.
 *)
let rec try_assum_progressT test goals tac p =
   let goal, assums = dest_msequent (Sequent.msequent p) in
   let rec expand i = function
      _ :: assums ->
         if not (test i p) or check_hyp_progress i goal goals then
            expand (i + 1) assums
         else
            let item = tac i, AutoTac (try_assum_progressT test ((i, goal) :: goals) tac) in
               item :: expand (i + 1) assums
    | [] ->
         []
   in
      expand 1 assums

let auto_assum_progress test (tac : int -> tactic) =
   AutoTac (try_assum_progressT test [] tac)

(*
 * Trivial tactic.
 *)
let trivialT p =
   get_resource_arg p get_trivial_resource p

(*
 * Trivial is in auto tactic.
 *)
let trivial_prec = create_auto_prec [] []

(*
 * Some trivial tactics.
 *)
let resource trivial += {
   auto_name = "nthAssumT";
   auto_prec = trivial_prec;
   auto_tac = onSomeAssumT nthAssumT
}

(*
 * Auto tactic includes trivialT.
 *)
let resource auto += {
   auto_name = "trivial";
   auto_prec = trivial_prec;
   auto_tac = auto_wrap trivialT
}

(*
 * The inherited auto tactic.
 *)
let autoT p =
   get_resource_arg p get_auto_resource p

let tryAutoT tac =
   tac thenT tryT (completeT autoT)

let byDefT conv =
   rwhAllAll (conv thenC reduceC) thenT autoT

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
