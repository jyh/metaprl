(*
 * This is the basic rewrite data type.
 * A file with this name is required for every theory.
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

include Perv

open Printf
open Mp_debug

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermAddr
open Refiner.Refiner.RefineError
open Refiner.Refiner.Rewrite
open Refiner.Refiner.Refine

open Tactic_type
open Sequent
open Var

let debug_rewrite = load_debug "rewrite"

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * A conversion is wither a regular rewrite,
 * or a conditional rewrite, or a composition.
 *
 * NOTE: we need to use a better data structure for
 * Compose and Choose that has more efficient
 * operations.
 *)
type conv = Tactic_type.conv

type env = Tactic_type.env

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Justification for rewrites.
 *)
declare rewrite_just

(*
 * The basic rewrite axiom.
 * BUG: jyh: I don't know why we need the extra param here.
 *)
prim rewriteAxiom 'a : : "rewrite"{'x; 'x} = rewrite_just

(*
 * Sequent version of rewrite proposition.
 *)
prim rewriteSequentAxiom 'H : :
   sequent ['ext] { 'H >- "rewrite"{'x; 'x} } =
   rewrite_just

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Get the term of the environment.
 *)
let env_term (arg, addr) =
   term_subterm (Sequent.goal arg) addr

let env_term_subterm_count (arg, addr) =
   term_subterm_count (Sequent.goal arg) addr

let env_arg (arg, addr) =
   arg

let get_conv = Tactic_type.get_conv
let conv_attribute = Tactic_type.conv_attribute

(*
 * Get the sequent that we are matching against.
 *)
let env_goal (arg, _) =
   Sequent.goal arg

(*
 * Create a conversion from a basic rewrite.
 * This function is required by filter_prog.
 *)
let rewrite_of_rewrite rw =
   RewriteConv rw

(*
 * Create a conversion from a conditional rewrite.
 * This function is required by filter_prog.
 *)
let rewrite_of_cond_rewrite crw args =
   CondRewriteConv (crw args)

(*
 * Combine two lissts of conversion.
 * Note if the adjacent conversion can be combined.
 *)
let combine rw_f crw_f make clist1 clist2 =
   match Flist.last clist1, Flist.first clist2 with
      RewriteConv rw1, RewriteConv rw2 ->
         let rw = RewriteConv (rw_f rw1 rw2) in
            if Flist.singleton clist1 & Flist.singleton clist2 then
               rw
            else
               make (Flist.append_skip clist1 rw clist2)
    | CondRewriteConv crw1, CondRewriteConv crw2 ->
         let crw = CondRewriteConv (crw_f crw1 crw2) in
            if Flist.singleton clist1 & Flist.singleton clist2 then
               crw
            else
               make (Flist.append_skip clist1 crw clist2)
    | _ ->
         make (Flist.append clist1 clist2)

let compose clist1 clist2 =
   combine andthenrw candthenrw (fun l -> ComposeConv l) clist1 clist2

let choose clist1 clist2 =
   combine orelserw corelserw (fun l -> ChooseConv l) clist1 clist2

let prefix_andthenC conv1 conv2 =
   let clist1 =
      match conv1 with
         ComposeConv clist1 ->
            clist1
       | _ ->
            Flist.create conv1
   in
   let clist2 =
      match conv2 with
         ComposeConv clist2 ->
            clist2
       | _ ->
            Flist.create conv2
   in
      compose clist1 clist2

let prefix_orelseC conv1 conv2 =
   let clist1 =
      match conv1 with
         ChooseConv clist1 ->
            clist1
       | _ ->
            Flist.create conv1
   in
   let clist2 =
      match conv2 with
         ChooseConv clist2 ->
            clist2
       | _ ->
            Flist.create conv2
   in
      choose clist1 clist2

(*
 * No action.
 *)
let idC = IdentityConv

(*
 * Function conversion needs an argument.
 *)
let funC f =
   FunConv f

(*
 * Apply the conversion at the specified address.
 *)
let addrC addr =
   let addr = make_address addr in
      (function
         RewriteConv rw ->
            RewriteConv (rwaddr addr rw)
       | CondRewriteConv crw ->
            CondRewriteConv (crwaddr addr crw)
       | conv ->
            AddressConv (addr, conv))

(*
 * Apply the conversion at the highest addresses.
 *)
let higherC = function
   RewriteConv rw ->
      RewriteConv (rwhigher rw)
 | CondRewriteConv crw ->
      CondRewriteConv (crwhigher crw)
 | conv ->
      HigherConv conv

let allSubC conv =
   let allSubCE conv env =
      let count = env_term_subterm_count env in
      let rec subC conv count i =
         if i = count then
            idC
         else
            (addrC [i] conv) andthenC (subC conv count (i + 1))
      in
         subC conv count 0
   in
      funC (allSubCE conv)

let higherLC rw =
   let rec higherCE rw env =
      (rw orelseC (allSubC (funC (higherCE rw))))
   in
      funC (higherCE rw)

(*
 * Reverse the conversion at the specified address.
 *)
let foldC t conv =
   FoldConv (t, conv)

(*
 * Build a fold conversion from the contractum
 * and the unfolding conversion.
 *)
let makeFoldC contractum conv =
   let fold_aux = function
      RewriteConv rw ->
         let mseq = mk_msequent contractum [] in
         let tac = rwtactic rw in
            begin
               (* Apply the unfold conversion *)
               match Refine.refine any_sentinal tac mseq with
                  [redex], _ ->
                     (* Unfolded it, so create a rewrite that reverses it *)
                     let redex, _ = dest_msequent redex in
                     let rw' = term_rewrite ([||], [||]) [redex] [contractum] in
                     let doCE env =
                        match apply_rewrite rw' ([||], [||], []) (env_term env) [] with
                           [contractum], _ ->
                              FoldConv (contractum, conv)
                         | _ ->
                              raise (RefineError ("Rewrite_type.fold", StringTermError ("rewrite failed", redex)))
                     in
                        FunConv doCE
                | _ ->
                     raise (RefineError ("Rewrite_type.fold", StringTermError ("fold failed", contractum)))
            end
    | _ ->
         raise (RefineError ("Rewrite_type.fold", StringError "can't fold nontrivial rewrites"))
   in
      Refine_exn.print Dform.null_base fold_aux conv

(*
 * Cut just replaces the term an generates a rewrite
 * subgoal.
 *)
let cutC t =
   CutConv t

(*
 * Apply axiom rule.
 *)
let rwAxiomT =
   rewriteAxiom << "string"["bogus argument"] >>

(*
 * Apply sequent axiom rule.
 *)
let rwSeqAxiomT p =
   rewriteSequentAxiom (Sequent.hyp_count_addr p) p

let rewrite_axiom = rwSeqAxiomT

(*
 * root: address of the clause
 * rel: offset into the term
 * addr: compose_addrress root rel
 *)
let rec apply rel addr conv p =
   match conv with
      RewriteConv rw ->
         if !debug_rewrite then
            eprintf "Rewrite_type.apply: Rewrite%t" eflush;
         Tactic_type.tactic_of_rewrite (rwaddr addr rw) p
    | CondRewriteConv crw ->
         if !debug_rewrite then
            eprintf "Rewrite_type.apply: CondRewrite%t" eflush;
         Tactic_type.tactic_of_cond_rewrite (crwaddr addr crw) p
    | ComposeConv clist ->
         if !debug_rewrite then
            eprintf "Rewrite_type.apply: Compose%t" eflush;
         composeT rel addr (Flist.tree_of_list clist) p
    | ChooseConv clist ->
         if !debug_rewrite then
            eprintf "Rewrite_type.apply: Choose%t" eflush;
         chooseT rel addr (Flist.tree_of_list clist) p
    | AddressConv (addr', conv) ->
         let rel = compose_address rel addr' in
         let addr = compose_address addr addr' in
            if !debug_rewrite then
               eprintf "Rewrite_type.apply: Address %s%t" (string_of_address addr') eflush;
            apply rel addr conv p
    | IdentityConv ->
         if !debug_rewrite then
            eprintf "Rewrite_type.apply: Identity%t" eflush;
         idT p
    | FunConv f ->
         if !debug_rewrite then
            eprintf "Rewrite_type.apply: Fun%t" eflush;
         apply rel addr (f (p, addr)) p
    | HigherConv conv ->
         if !debug_rewrite then
            eprintf "Rewrite_type.apply: Higher%t" eflush;
         apply rel addr (higherLC conv) p
    | FoldConv (t, conv) ->
         if !debug_rewrite then
            eprintf "Rewrite_type.apply: Fold%t" eflush;
         (Tactic_type.tactic_of_cond_rewrite (crwaddr addr (cutrw t))
          thenLT [idT; solveCutT conv]) p
    | CutConv t ->
         if !debug_rewrite then
            eprintf "Rewrite_type.apply: Cut%t" eflush;
         Tactic_type.tactic_of_cond_rewrite (crwaddr addr (cutrw t)) p

and composeT rel addr tree p =
   match tree with
      Flist.Empty ->
         idT p
    | Flist.Leaf conv ->
         apply rel addr conv p
    | Flist.Append (tree1, tree2) ->
         (composeT rel addr tree1
          thenT composeT rel addr tree2) p

and chooseT rel addr tree p =
   match tree with
      Flist.Empty ->
         idT p
    | Flist.Leaf conv ->
         apply rel addr conv p
    | Flist.Append (tree1, tree2) ->
         (chooseT rel addr tree1
          orelseT chooseT rel addr tree2) p

and solveCutT conv p =
   let rel = make_address [0] in
   let root = Sequent.clause_addr p 0 in
   let addr = compose_address root rel in
      (apply rel addr conv thenT rwSeqAxiomT) p

(*
 * Apply the rewrite.
 *)
let rw conv i p =
   if !debug_rewrite then
      eprintf "Rewrite start%t" eflush;
   let addr = Sequent.clause_addr p i in
   let x = apply (make_address []) addr conv p in
      if !debug_rewrite then
         eprintf "Rewrite done%t" eflush;
      x

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
