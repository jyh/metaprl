(*
 * This is a simple-minded auto tactic that recursively tries
 * all the of tactics given.
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
 *)

include Mptop
include Summary

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

type 'a auto_data =
   Empty
 | Tactic of 'a auto_info * 'a auto_data
 | Remove of auto_prec * 'a auto_data
 | Label of 'a auto_data
 | Join of 'a auto_data * 'a auto_data

resource (tactic auto_info, tactic, tactic auto_data, Tactic.pre_tactic * auto_prec) trivial_resource
resource (auto_tac auto_info, tactic, auto_tac auto_data, Tactic.pre_tactic * auto_prec) auto_resource

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
let extract compile info =
   let rec collect joins removes tactics item =
      match item with
         Empty ->
            joins, removes, tactics
       | Tactic (info, next) ->
            if node_member info.auto_prec removes then
               collect joins removes tactics next
            else
               collect joins removes (info :: tactics) next
       | Remove (node, next) ->
            collect joins (node :: removes) tactics next
       | Label next ->
            if List.memq item joins then
               joins, removes, tactics
            else
               collect (item :: joins) removes tactics next
       | Join (base1, base2) ->
            let joins, removes, tactics = collect joins removes tactics base1 in
               collect joins removes tactics base2
   in
   let _, _, tactics = collect [] [] [] info in
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

(*
 * Wrap up the joiner.
 *)
let join_resource data1 data2 =
   Join (data1, data2)

let improve_resource data info =
   if !debug_auto then
      eprintf "Base_auto_tactic.improve_resource: adding %s%t" info.auto_name eflush;
   Tactic (info, data)

let make_auto_tactic name context_args var_args term_args pre_tactic =
   match context_args, term_args with
      [| _ |], [] ->
         (fun p ->
               let vars = Var.maybe_new_vars_array p var_args in
               let addr = Sequent.hyp_count_addr p in
                  Tactic_type.Tactic.tactic_of_rule pre_tactic ([| addr |], vars) [] p)
    | _, [] ->
         raise (Invalid_argument (sprintf "Base_auto_tactic.improve: %s: only introduction rules are allowed" name))
    | _ ->
         raise (Invalid_argument (sprintf "Base_auto_tactic.improve: %s: term arguments are not allowed in auto tactics" name))

let improve_triv_resource_arg data name context_args var_args term_args _ _ (pre_tactic, tprec) =
   let tac = make_auto_tactic name context_args var_args term_args pre_tactic in
   let info = { auto_name = name; auto_prec = tprec; auto_tac = tac } in
      Tactic (info, data)

let improve_auto_resource_arg data name context_args var_args term_args _ _ (pre_tactic, tprec) =
   let tac = make_auto_tactic name context_args var_args term_args pre_tactic in
   let info = { auto_name = name; auto_prec = tprec; auto_tac = auto_wrap tac } in
      Tactic (info, data)

let close_resource data modname =
   Label data

(*
 * Resource.
 *)
let extract_triv_resource data =
   extract compileTrivialT data

let trivial_resource =
   Mp_resource.create (**)
      { resource_join = join_resource;
        resource_extract = extract_triv_resource;
        resource_improve = improve_resource;
        resource_improve_arg = improve_triv_resource_arg;
        resource_close = close_resource
      }
      Empty

let extract_auto_resource data =
   extract compileAutoT data

let auto_resource =
   Mp_resource.create (**)
      { resource_join = join_resource;
        resource_extract = extract_auto_resource;
        resource_improve = improve_resource;
        resource_improve_arg = improve_auto_resource_arg;
        resource_close = close_resource
      }
      Empty

(*
 * Create a precedence.
 *)
let create_auto_prec before after =
   let node = ImpDag.insert dag () in
      List.iter (fun p -> ImpDag.add_edge dag p node) before;
      List.iter (fun p -> ImpDag.add_edge dag node p) after;
      node

(*
 * Remove all tactics with a given precedence.
 *)
let remove_auto_tactic auto_rsrc node =
   let wrap items =
      Remove (node, items)
   in
      Mp_resource.wrap auto_rsrc wrap

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
   Sequent.get_tactic_arg p "trivial" p

(*
 * Trivial is in auto tactic.
 *)
let trivial_prec = create_auto_prec [] []

(*
 * Some trivial tactics.
 *)
let trivial_resource =
   Mp_resource.improve trivial_resource (**)
      { auto_name = "nthAssumT";
        auto_prec = trivial_prec;
        auto_tac = onSomeAssumT nthAssumT
      }

let get_trivial_resource modname =
   Mp_resource.find trivial_resource modname

(*
 * Auto tactic includes trivialT.
 *)
let auto_resource =
   Mp_resource.improve auto_resource (**)
      { auto_name = "trivial";
        auto_prec = trivial_prec;
        auto_tac = auto_wrap trivialT
      }

let get_auto_resource modname =
   Mp_resource.find auto_resource modname

(*
 * The inherited auto tactic.
 *)
let autoT p =
   Sequent.get_tactic_arg p "auto" p

let tryAutoT tac =
   tac thenT tryT (completeT autoT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
