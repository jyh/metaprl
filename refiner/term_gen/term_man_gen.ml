(*
 * Manifest terms.
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
 * Modified by: Alexey Nogin
 *)

INCLUDE "refine_error.mlh"

open Printf
open Mp_debug

open Opname
open Refine_error_sig
open Term_simple_sig
open Term_base_sig
open Term_op_sig
open Term_addr_sig
open Term_subst_sig

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Term_man_gen%t" eflush

let debug_address =
   create_debug (**)
      { debug_name = "address";
        debug_description = "show term addressing operations";
        debug_value = false
      }

(*
 * Module builds on term implementation.
 *)
module TermMan (**)
   (Term : TermSimpleSig)
   (TermBase : TermBaseSig
    with type term = Term.term
    with type term' = Term.term'
    with type bound_term = Term.bound_term
    with type bound_term' = Term.bound_term'
    with type operator = Term.operator
    with type operator' = Term.operator'
    with type hypothesis = Term.hypothesis
    with type seq_hyps = Term.seq_hyps
    with type seq_goals = Term.seq_goals)
   (TermOp : TermOpSig
    with type term = Term.term)
   (TermAddr : TermAddrSig
    with type term = Term.term)
   (TermSubst : TermSubstSig
    with type term = Term.term
    with type param = Term.param)
   (RefineError : RefineErrorSig
    with type term = Term.term
    with type address = TermAddr.address) =
struct
   open Term
   open TermBase
   open TermOp
   open TermAddr
   open TermSubst
   open RefineError

   type term = Term.term
   type operator = Term.operator
   type level_exp = Term.level_exp
   type address = TermAddr.address

   type esequent = Term.esequent

   (************************************************************************
    * Level expressions                                                    *
    ************************************************************************)

   (* Simplified level expression constructors *)
   let mk_const_level_exp i =
      { le_const = i; le_vars = [] }

   let mk_var_level_exp v =
      { le_const = 0; le_vars = [{ le_var = v; le_offset = 0 }] }

   (*
    * Increment a level exp
    *)
   let incr_level_exp = function
      ({ le_const = c; le_vars = vars } : level_exp) ->
         let add1 = function
            { le_var = v; le_offset = o } ->
               { le_var = v; le_offset = o + 1 }
         in
            { le_const = c + 1; le_vars = List.map add1 vars }

   (*
    * Build a level expression out of the max of two level
    * expressions.
    *)
   let max_level_exp
      ({ le_const = c1; le_vars = l1 } : level_exp)
      ({ le_const = c2; le_vars = l2 } : level_exp)
      o3 =
         (* Max of two expressions; sort the variables *)
         let rec join = function
            ({ le_var = v1; le_offset = o1 } as h1::t1 as l1),
            ({ le_var = v2; le_offset = o2 } as h2::t2 as l2) ->
               if v1 = v2 then
                  { le_var = v1; le_offset = max o1 (o2 + o3) } :: join (t1, t2)
               else if v1 < v2 then
                  h1 :: join (t1, l2)
               else if o3 = 0 then
                  h2 :: join (l1, t2)
               else
                  { le_var = v2; le_offset = o2 + o3 } :: join (l1, t2)
          | [], l2 ->
               if o3 = 0 then
                  l2
               else
                  let add_off { le_var = v2; le_offset = o2 } =
                     { le_var = v2; le_offset = o2 + o3 }
                  in
                     List.map add_off l2
          | l1, [] ->
               l1
         in
            { le_const = max c1 (c2 + o3); le_vars = join (l1, l2) }

   (*
    * See if the first level is contained in the second.
    *)
   let level_le = fun
      { le_const = const1; le_vars = vars1 }
      { le_const = const2; le_vars = vars2 } ->
         let rec caux = function
            ({ le_var = v1; le_offset = o1 }::t1 as l1),
            { le_var = v2; le_offset = o2 }::t2 ->
               if v1 = v2 then
                  if o1 <= o2 then
                     caux (t1, t2)
                  else
                     false
               else if v2 < v1 then
                  caux (l1, t2)
               else
                  false
          | [], _ -> true
          | _, [] -> false
         in
            if const1 <= const2 then
               caux (vars1, vars2)
            else
               false

   let level_lt = fun
      { le_const = const1; le_vars = vars1 }
      { le_const = const2; le_vars = vars2 } ->
         let rec caux = function
            ({ le_var = v1; le_offset = o1 }::t1 as l1),
            { le_var = v2; le_offset = o2 }::t2 ->
               if v1 = v2 then
                  if o1 < o2 then
                     caux (t1, t2)
                  else
                     false
               else if v2 < v1 then
                  caux (l1, t2)
               else
                  false
          | [], _ ->
               true
          | _, [] ->
               false
         in
            if const1 < const2 then
               caux (vars1, vars2)
            else
               false

   (************************************************************************
    * PRIMITIVE FORMS                                                      *
    ************************************************************************)

   (*
    * Lists.
    *)
   let xnil_opname = mk_opname "nil" xperv
   let xcons_opname = mk_opname "cons" xperv

   let xnil_term = mk_simple_term xnil_opname []
   let is_xnil_term t = t = xnil_term

   let is_xcons_term = is_dep0_dep0_term xcons_opname
   let mk_xcons_term = mk_dep0_dep0_term xcons_opname
   let dest_xcons = dest_dep0_dep0_term xcons_opname

   let rec is_xlist_term t =
      match dest_term t with
         { term_op = { op_name = opname; op_params = [] };
           term_terms = [bterm1; bterm2]
         } when Opname.eq opname xcons_opname ->
            begin
               match (dest_bterm bterm1, dest_bterm bterm2) with
                  ({ bvars = []; bterm = _ }, { bvars = []; bterm = b }) ->
                     is_xlist_term b
                | _ ->
                     false
            end
       | { term_op = { op_name = opname; op_params = [] }; term_terms = [] } when Opname.eq opname xnil_opname ->
            true
       | _ ->
            false

   let dest_xlist t =
      let rec aux trm =
         match dest_term trm with
            { term_op = { op_name = opname; op_params = [] };
              term_terms = [bterm1; bterm2]
            } when Opname.eq opname xcons_opname ->
               begin
                  match (dest_bterm bterm1, dest_bterm bterm2) with
                     ({ bvars = []; bterm = a },
                      { bvars = []; bterm = b }) -> a::(aux b)
                   | _ -> REF_RAISE(RefineError ("dest_xlist", TermMatchError (t, "not a list")))
               end
          | { term_op = { op_name = opname; op_params = [] }; term_terms = [] } when Opname.eq opname xnil_opname ->
               []
          | _ ->
               REF_RAISE(RefineError ("dest_xlist", TermMatchError (t, "not a list")))
      in
         aux t

   let rec mk_xlist_term = function
      h::t ->
         mk_term (**)
            { op_name = xcons_opname; op_params = [] }
            [mk_simple_bterm h; mk_simple_bterm (mk_xlist_term t)]
    | [] ->
         xnil_term

   (*
    * Strings.
    *)
   let string_opname = mk_opname "string" xperv

   let is_xstring_term t =
      match dest_term t with
         { term_op = { op_name = opname; op_params = [String _] };
           term_terms = []
         } when Opname.eq opname string_opname ->
            true
       | _ ->
            false

   let dest_xstring t =
      match dest_term t with
         { term_op = { op_name = opname; op_params = [String s] };
           term_terms = []
         } when Opname.eq opname string_opname ->
            s
       | _ ->
            REF_RAISE(RefineError ("dest_xstring", TermMatchError (t, "not a string")))

   let mk_xstring_term s =
      let op = { op_name = string_opname; op_params = [String s] } in
         mk_term op []

   (*
    * String with one subterm.
    *)
   let is_xstring_dep0_term t =
      match dest_term t with
         { term_op = { op_name = opname; op_params = [String _] };
           term_terms = [bt]
         } when Opname.eq opname string_opname ->
            begin
               match dest_bterm bt with
                  { bvars = []; bterm = _ } ->
                     true
                | _ ->
                     false
            end
       | _ ->
            false

   let dest_xstring_dep0_term t =
      match dest_term t with
         { term_op = { op_name = opname; op_params = [String s] };
           term_terms = [bt]
         } when Opname.eq opname string_opname ->
            begin
               match dest_bterm bt with
                  { bvars = []; bterm = t } ->
                     s, t
                | _ ->
                     REF_RAISE(RefineError ("dest_xstring_dep0_term", TermMatchError (t, "not a string with one subterm")))
            end
       | _ ->
            REF_RAISE(RefineError ("dest_xstring_dep0_term", TermMatchError (t, "not a string with one subterm")))

   let mk_xstring_dep0_term s t =
      let op = { op_name = string_opname; op_params = [String s] } in
         mk_term op [mk_bterm [] t]

   (****************************************
    * LAMBDA                               *
    ****************************************)

   let xlambda_opname = mk_opname "lambda" xperv
   let mk_xlambda_term = mk_dep1_term xlambda_opname

   (*************************
    * Sequents              *                                              *
    *************************)

   (* Sequent operator names *)
   let hyp_opname = mk_opname "hyp" xperv
   let concl_opname = mk_opname "concl" xperv

   (* Sequent wrapper *)
   let is_sequent_term = is_simple_term_opname sequent_opname

   (* Dependent hypotheses *)
   let is_hyp_term = is_dep0_dep1_term hyp_opname
   let mk_hyp_term = mk_dep0_dep1_term hyp_opname
   let dest_hyp = dest_dep0_dep1_term hyp_opname

   (* Conclusions *)
   let is_concl_term = is_dep0_dep0_term concl_opname
   let mk_concl_term = mk_dep0_dep0_term concl_opname
   let dest_concl = dest_dep0_dep0_term concl_opname
   let null_concl = mk_simple_term concl_opname []

   let mk_sequent_outer_term goal args =
      mk_simple_term sequent_opname [args; goal]

   let rec mk_goals goals i len =
      if i = len then
         null_concl
      else
         mk_concl_term (SeqGoal.get goals i) (mk_goals goals (i + 1) len)

   let rec mk_sequent_inner_term hyps goals i len =
      if i = len then
         mk_goals goals 0 (SeqGoal.length goals)
      else
         match SeqHyp.get hyps i with
            Hypothesis (v, t') ->
               mk_hyp_term v t' (mk_sequent_inner_term hyps goals (i + 1) len)
          | Context (v, subterms) ->
               mk_context_term v (mk_sequent_inner_term hyps goals (i + 1) len) subterms

   let mk_sequent_term
       { sequent_args = args;
         sequent_hyps = hyps;
         sequent_goals = goals
       } =
      mk_sequent_outer_term (mk_sequent_inner_term hyps goals 0 (SeqHyp.length hyps)) args

   let dest_sequent_outer_term seq =
      match dest_simple_term_opname sequent_opname seq with
         [args; goal] ->
            goal, args
       | _ ->
            REF_RAISE(RefineError ("dest_sequent", TermMatchError (seq, "sequent must have two subterms")))

   let args_of_sequent seq =
      match dest_simple_term_opname sequent_opname seq with
         [args; _] ->
            args
       | _ ->
            REF_RAISE(RefineError ("args_of_sequent", TermMatchError (seq, "sequent must have two subterms")))

   (*
    * Helper function to unwrap the surrounding sequent term.
    *)
   let goal_of_sequent t =
      match dest_term t with
         { term_op = { op_name = name; op_params = [] };
           term_terms = [_; bgoal]
         } when Opname.eq name sequent_opname ->
            dest_simple_bterm bgoal
       | _ ->
            REF_RAISE(RefineError ("goal_of_sequent", TermMatchError (t, "not a sequent")))

   (*
    * Get the second term in the hyp.
    *)
   let match_hyp name t = function
      [bterm1; bterm2] ->
         begin
            match dest_bterm bterm1, dest_bterm bterm2 with
               ({ bvars = [] }, { bvars = [_]; bterm = term }) ->
                  term
             | _ ->
                  REF_RAISE(RefineError (name, TermMatchError (t, "malformed hypothesis")))
         end
    | _ ->
         REF_RAISE(RefineError (name, TermMatchError (t, "malformed hypothesis")))

   let match_hyp_all name t = function
      [bterm1; bterm2] ->
         begin
            match dest_bterm bterm1, dest_bterm bterm2 with
               ({ bvars = []; bterm = t }, { bvars = [x]; bterm = term }) ->
                  t, x, term
             | _ ->
                  REF_RAISE(RefineError (name, TermMatchError (t, "malformed hypothesis")))
         end
    | _ ->
         REF_RAISE(RefineError (name, TermMatchError (t, "malformed hypothesis")))

   let match_context name t = function
      [] ->
         REF_RAISE(RefineError (name, TermMatchError (t, "malformed context")))
    | bterms ->
         match dest_bterm (List_util.last bterms) with
            { bvars = []; bterm = term } ->
               term
          | _ ->
               REF_RAISE(RefineError (name, TermMatchError (t, "malformed context")))

   let match_concl name t = function
      [bterm1; bterm2] ->
         begin
            match dest_bterm bterm1, dest_bterm bterm2 with
               ({ bvars = [] }, { bvars = []; bterm = term }) ->
                  term
             | _ ->
                  REF_RAISE(RefineError (name, TermMatchError (t, "malformed conclusion")))
         end
    | _ ->
         REF_RAISE(RefineError (name, TermMatchError (t, "malformed conclusion")))

   let match_concl_all name t = function
      [bterm1; bterm2] ->
         begin
            match dest_bterm bterm1, dest_bterm bterm2 with
               ({ bvars = []; bterm = t }, { bvars = []; bterm = term }) ->
                  t, term
             | _ ->
                  REF_RAISE(RefineError (name, TermMatchError (t, "malformed conclusion")))
         end
    | _ ->
         REF_RAISE(RefineError (name, TermMatchError (t, "malformed conclusion")))

   (*
    * Explode the sequent into a list of hyps and concls.
    *)
   let explode_sequent_name = "explode_sequent"
   let explode_sequent t =
      let rec collect (args : term) hyps concls term =
         let { term_op = { op_name = opname }; term_terms = bterms } = dest_term term in
            if Opname.eq opname hyp_opname then
               let t, x, term = match_hyp_all explode_sequent_name t bterms in
                  collect args (Hypothesis (x, t) :: hyps) concls term
            else if Opname.eq opname context_opname then
               let name, term, args' = dest_context term in
                  collect args (Context (name, args') :: hyps) concls term
            else if Opname.eq opname concl_opname then
               if bterms = [] then
                  { sequent_args = args;
                    sequent_hyps =  SeqHyp.of_list (List.rev hyps);
                    sequent_goals = SeqGoal.of_list (List.rev concls)
                  }
               else
                  let goal, term = match_concl_all explode_sequent_name t bterms in
                     collect args hyps (goal :: concls) term
            else
               REF_RAISE(RefineError (explode_sequent_name, TermMatchError (t, "malformed sequent")))
      in
      let goal, args = dest_sequent_outer_term t in
         collect args [] [] goal

   (*
    * Find the address of the hyp.
    * We just check to make sure the address is valid.
    * Hyps are numbered from 1.
    *)
   let nth_hyp_addr_name = "nth_hyp_addr"
   let nth_hyp_addr t n =
      let n = pred n in
      let addr = nth_hd_address n in
      let rec skip_hyps i term =
         let { term_op = { op_name = opname }; term_terms = bterms } = dest_term term in
            if Opname.eq opname hyp_opname then
               let term = match_hyp nth_hyp_addr_name t bterms in
                  if i = 0 then
                     addr
                  else
                     skip_hyps (i - 1) term
            else if Opname.eq opname context_opname then
               let term = match_context nth_hyp_addr_name t bterms in
                  if i = 0 then
                     addr
                  else
                     skip_hyps (i - 1) term
            else
               REF_RAISE(RefineError (nth_hyp_addr_name, TermMatchError (t, "not enough hyps")))
      in
         skip_hyps n (goal_of_sequent t)

   (*
    * Find the address of the conclusion.
    * This is the address of the concl term whose car is the desired conclusion
    * not the conclusion itself.
    *
    * Conclusions are numbered from 1.
    *)
   let nth_concl_addr_name = "nth_concl_addr"
   let nth_concl_addr t n =
      let rec skip_concl i n term =
         if n <= 1 then
            nth_tl_address i
         else
            match dest_term term with
               { term_op = { op_name = opname };
                 term_terms = [bterm1; bterm2]
               } when Opname.eq opname concl_opname ->
                  begin
                     match dest_bterm bterm1, dest_bterm bterm2 with
                        ({ bvars = [] }, { bvars = []; bterm = term }) ->
                           skip_concl (i + 1) (n - 1) term
                      | _ ->
                           REF_RAISE(RefineError (nth_concl_addr_name, TermMatchError (t, "malformed conclusion")))
                  end
             | _ ->
                  REF_RAISE(RefineError (nth_concl_addr_name, (TermMatchError (t, "malformed conclusion"))))
      in
      let rec skip_hyps i term =
         let { term_op = { op_name = opname }; term_terms = bterms } = dest_term term in
            if Opname.eq opname hyp_opname then
               let term = match_hyp nth_concl_addr_name t bterms in
                  skip_hyps (i + 1) term
            else if Opname.eq opname context_opname then
               let term = match_context nth_concl_addr_name t bterms in
                  skip_hyps (i + 1) term
            else if Opname.eq opname concl_opname then
               let term = match_concl nth_concl_addr_name t bterms in
                  skip_concl i n term
            else
               REF_RAISE(RefineError (nth_concl_addr_name, TermMatchError (t, "malformed sequent")))
      in
         skip_hyps 0 (goal_of_sequent t)

   (*
    * Conclusion is number 0,
    * negative numbers index from last hyp towards first.
    *)
   let nth_clause_addr_name = "nth_clause_addr"
   let nth_clause_addr_aux make_address t =
      let rec aux i term =
         let { term_op = { op_name = opname }; term_terms = bterms } = dest_term term in
            if Opname.eq opname hyp_opname then
               let term = match_hyp nth_clause_addr_name t bterms in
                  aux (i + 1) term
            else if Opname.eq opname context_opname then
               let term = match_context nth_clause_addr_name t bterms in
                  aux (i + 1) term
            else if Opname.eq opname concl_opname then
               make_address i
            else
               REF_RAISE(RefineError (nth_clause_addr_name, TermMatchError (t, "malformed sequent")))
      in
         aux 1 (goal_of_sequent t)

   let make_nth_clause_addr nth_address count i =
      if i < 0 then
         nth_address (count + i)
      else if i = 0 then
         nth_address count
      else
         nth_address i

   let nth_clause_addr t i =
      nth_clause_addr_aux (fun count -> make_nth_clause_addr nth_hd_address count i) t

   (*
    * Count the hyps.
    *)
   let num_hyps_name = "num_hyps"

   let num_hyps t =
      let rec aux i term =
         let { term_op = { op_name = opname }; term_terms = bterms } = dest_term term in
            if Opname.eq opname hyp_opname then
               let term = match_hyp num_hyps_name t bterms in
                  aux (i + 1) term
            else if Opname.eq opname context_opname then
               let term = match_context num_hyps_name t bterms in
                  aux (i + 1) term
            else if Opname.eq opname concl_opname then
               i
            else
               REF_RAISE(RefineError (num_hyps_name, TermMatchError (t, "malformed sequent")))
      in
         aux 0 (goal_of_sequent t)

   (*
    * Range functions for contexts in the sequent.
    * We don't check the values because we don't know
    * the position within the sequent.
    *)
   let hyp_range_addr t i =
      nth_tl_address i

   let hyp_indices_addr t i =
      let count = num_hyps t in
      if i < 0 then
         nth_tl_address (count + i), nth_tl_address ((-1) - i)
      else
         nth_tl_address (i - 1), nth_tl_address (count - i)

   let concl_range_addr t i =
      nth_tl_address i

   (*
    * Fast access to hyp and concl.
    *)
   let nth_hyp_name = "nth_hyp"
   let nth_hyp t i =
      let rec aux i term =
         let { term_op = { op_name = opname }; term_terms = bterms } = dest_term term in
            if Opname.eq opname hyp_opname then
               let t, x, term = match_hyp_all nth_hyp_name t bterms in
                  if i = 0 then
                     x, t
                  else
                     aux (i - 1) term
            else if Opname.eq opname context_opname then
               let term = match_context nth_hyp_name t bterms in
                  if i = 0 then
                     REF_RAISE(RefineError (nth_hyp_name, TermMatchError (t, "nth hyp is a context var")))
                  else
                     aux (i - 1) term
            else if Opname.eq opname concl_opname then
               REF_RAISE(RefineError ("nth_hyp", StringError "hyp is out of range"))
            else
               REF_RAISE(RefineError (nth_hyp_name, TermMatchError (t, "malformed sequent")))
      in
         aux (pred i) (goal_of_sequent t)

   let nth_concl_name = "nth_concl"
   let nth_concl t i =
      let rec aux i term =
         let { term_op = { op_name = opname }; term_terms = bterms } = dest_term term in
            if Opname.eq opname hyp_opname then
               let term = match_hyp nth_concl_name t bterms in
                  aux i term
            else if Opname.eq opname context_opname then
               let term = match_context nth_concl_name t bterms in
                  aux i term
            else if Opname.eq opname concl_opname then
               let t, term = match_concl_all nth_concl_name t bterms in
                  if i = 0 then
                     t
                  else
                     aux (i - 1) term
            else
               REF_RAISE(RefineError (nth_concl_name, TermMatchError (t, "malformed sequent")))
      in
         aux (pred i) (goal_of_sequent t)

   (*
    * Collect the vars.
    *)
   let declared_vars_name = "declared_vars"
   let declared_vars t =
      let rec aux vars term =
         let { term_op = { op_name = opname }; term_terms = bterms } = dest_term term in
            if Opname.eq opname hyp_opname then
               let _, x, term = match_hyp_all declared_vars_name t bterms in
                  aux (x :: vars) term
            else if Opname.eq opname context_opname then
               let term = match_context declared_vars_name t bterms in
                  aux vars term
            else if Opname.eq opname concl_opname then
               vars
            else
               REF_RAISE(RefineError (declared_vars_name, TermMatchError (t, "malformed sequent")))
      in
         aux [] (goal_of_sequent t)

   (*
    * Get the number of the hyp with the given var.
    *)
   let get_decl_number_name = "get_decl_number"

   let get_decl_number t v =
      let rec aux i term =
         let { term_op = { op_name = opname }; term_terms = bterms } = dest_term term in
            if Opname.eq opname hyp_opname then
               let _, x, term = match_hyp_all get_decl_number_name t bterms in
                  if x = v then
                     i
                  else
                     aux (i + 1) term
            else if Opname.eq opname context_opname then
               let term = match_context get_decl_number_name t bterms in
                  aux (i + 1) term
            else if Opname.eq opname concl_opname then
               REF_RAISE(RefineError (get_decl_number_name, TermMatchError (t, "declaration not found")))
            else
               REF_RAISE(RefineError (get_decl_number_name, TermMatchError (t, "malformed sequent")))
      in
         aux 1 (goal_of_sequent t)

   (*
    * See if a var is free in the rest of the sequent.
    *)
   let is_free_seq_var_name = "is_free_seq_var"
   let is_free_seq_var i v t =
      let rec aux i t =
         if i = 0 then
            is_free_var v t
         else
            let { term_op = { op_name = opname }; term_terms = bterms } = dest_term t in
               if Opname.eq opname hyp_opname then
                  let term = match_hyp is_free_seq_var_name t bterms in
                     aux (i - 1) term
               else if Opname.eq opname context_opname then
                  let term = match_context is_free_seq_var_name t bterms in
                     aux (i - 1) term
               else if Opname.eq opname concl_opname then
                  REF_RAISE(RefineError (is_free_seq_var_name, TermMatchError (t, "index is not a hypothesis")))
               else
                  REF_RAISE(RefineError (is_free_seq_var_name, TermMatchError (t, "malformed sequent")))
      in
         aux i (goal_of_sequent t)

   (*
    * Generate a list of sequents with replaced goals.
    *)
   let replace_concl_name = "replace_concl"
   let rec replace_concl seq goal =
      let { term_op = ({ op_name = opname } as op); term_terms = bterms } = dest_term seq in
         if Opname.eq opname hyp_opname then
            let t, x, term = match_hyp_all replace_concl_name seq bterms in
               mk_term op [mk_simple_bterm t; mk_bterm [x] (replace_concl term goal)]
         else if Opname.eq opname context_opname then
            let name, term, args = dest_context seq in
               mk_context_term name (replace_concl term goal) args
         else if Opname.eq opname concl_opname then
            goal
         else
            REF_RAISE(RefineError (replace_concl_name, TermMatchError (seq, "malformed sequent")))

   let replace_goal_name = "replace_goal"
   let replace_goal seq goal =
      let seq, args = dest_sequent_outer_term seq in
         mk_sequent_outer_term (replace_concl seq (mk_concl_term goal null_concl)) args

   (*
    * Rewrite
    *)
   let xrewrite_op = mk_opname "rewrite" xperv

   let is_xrewrite_term = is_dep0_dep0_term xrewrite_op
   let mk_xrewrite_term = mk_dep0_dep0_term xrewrite_op
   let dest_xrewrite = dest_dep0_dep0_term xrewrite_op

   (************************************************************************
    * Rewrite rules                                                        *
    ************************************************************************)

   (*
    * Build a redex.
    *)
   let construct_redex vars params terms =
      let t = mk_xlist_term (params @ terms) in
      let l = Array.length vars in
      let rec aux i =
         if i < l then
            mk_xlambda_term vars.(i) (aux (i + 1))
         else
            t
      in
         aux 0

end

