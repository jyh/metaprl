doc <:doc<
   @module["meta-context-ind1"]
   ``Teleportation'' model of context induction.

   This model is documented more precisely in
   @code{papers/notebook/context_induction}.

   At a high level, the mechanism works by ``teleporting'' a contex
   from one sequent to another.  Suppose we are proving
   a rule @code{S1 --> ... --> Sn(Gamma)} and we wish to do induction on
   Gamma.  For each occurrence of Gamma on which to do induction, specify
   a target location to shift Gamma into.  The target location may be in the
   scope of Gamma, or above the scope of Gamma, but everything in the scope
   of Gamma will remain so.  Then induction works by proving how to move
   Gamma from one location to another.

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2005 Mojave Group, Caltech

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Jason Hickey @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Meta_implies

doc docoff

open Term_man_sig
open Basic_tactics
open Refiner.Refiner.Refine

(************************************************************************
 * Types.
 *)

(*
 * The current processing state.
 *    StartState: initial state (XXX ... <src> ... <dst> ...)
 *    SrcState: between (... <src> ... XXX ... <dst> ...)
 *    DstState: between (... <dst> ... XXX ... <src> ...)
 *    FinalState: after (... <src> ... <dst> ... XXX ...)
 *)
type state =
   StartState
 | SrcState
 | DstState
 | FinalState

(*
 * The processing mode.
 *    BaseMode: produce the term for the base case
 *    LeftMode: left step term
 *    RightMode: right step term
 *    FinalMode: final term
 *)
type mode =
   BaseMode
 | LeftMode
 | RightMode
 | FinalMode

(*
 * Context variable classification.
 *)
type context_var =
   SrcVar
 | DstVar
 | NoVar

(************************************************************************
 * Term operations.
 *)

(*
 * Get the first context var in a sequent.
 *)
let context_var_of_sequent t =
   if is_sequent_term t then
      let hyps = (explode_sequent t).sequent_hyps in
         if SeqHyp.length hyps > 0 then
            match SeqHyp.get hyps 0 with
               Context (v, _, _) ->
                  v
             | Hypothesis _ ->
                  raise Not_found
         else
            raise Not_found
   else
      raise Not_found

let context_var_of_sequent t =
   try context_var_of_sequent t with
      Not_found ->
         raise (RefineError ("Meta_context_ind1", StringError "context_var_of_sequent: not a simple context sequent"))

(*
 * Simple var replacement.
 *)
let replace_var2 cs v1 v2 v3 =
   List.map (fun v ->
         if Lm_symbol.eq v v1 || Lm_symbol.eq v v2 then
            v3
         else
            v) cs

(*
 * Test whether any of the 3 vars occurs in the var list.
 *)
let mem_context3 cs v1 v2 v3 =
   List.exists (fun v -> Lm_symbol.eq v v1 || Lm_symbol.eq v v2 || Lm_symbol.eq v v3) cs

(*
 * Replace a var with two others in a var list.
 *)
let rec replace_context3 cs v1 v2 v3 cv1 cv2 =
   match cs with
      v :: cs ->
         if Lm_symbol.eq v v1 || Lm_symbol.eq v v2 || Lm_symbol.eq v v3 then
            cv1 :: cv2 :: cs
         else
            v :: replace_context3 cs v1 v2 v3 cv1 cv2
    | [] ->
         raise Not_found

let replace_context3 cs v1 v2 v3 cv1 cv2 =
   try Some (replace_context3 cs v1 v2 v3 cv1 cv2) with
      Not_found ->
         None

(*
 * Remove the special context vars.
 *)
let rec remove_context_vars cs v1 v2 =
   match cs with
      v :: cs ->
         if Lm_symbol.eq v v1 || Lm_symbol.eq v v2 then
            remove_context_vars cs v1 v2
         else
            v :: remove_context_vars cs v1 v2
    | [] ->
         []

(*
 * Choose the var.
 *)
let context_var_mode v vsrc vdst =
   if Lm_symbol.eq v vsrc then
      SrcVar
   else if Lm_symbol.eq v vdst then
      DstVar
   else
      NoVar

(************************************************************************
 * Subgoal term generators.
 *)

(*
 * State transitions.
 *)
let state_trans state var_mode =
   match state, var_mode with
      StartState, SrcVar ->
         SrcState
    | StartState, DstVar ->
         DstState
    | SrcState, DstVar
    | DstState, SrcVar ->
         FinalState
    | _, NoVar ->
         state
    | SrcState, SrcVar
    | DstState, DstVar
    | FinalState, SrcVar
    | FinalState, DstVar ->
         raise (RefineError ("Meta_context_ind1.state_trans", StringError "repeated context variable"))

(*
 * Generalize to the left version of the term.
 *
 *    mode: one of the replacement modes
 *    v: the original context var
 *    vsrc: the src context var
 *    vdst: the target context var
 *    cv1, x, cv2: the context it is being replaced with
 *    info: the map to new variable names
 *
 *)
let generalize_term t v vsrc vdst cv1 x x_A cv2 info mode =
   let x_t = mk_var_term x in
   let rec generalize_term state t =
      if is_var_term t then
         t
      else if is_so_var_term t then
         generalize_so_var_term state t
      else if is_context_term t then
         generalize_context_term state t
      else if is_sequent_term t then
         generalize_sequent_term state t
      else
         let { term_op = op; term_terms = bterms } = dest_term t in
         let bterms = generalize_bterm_list state bterms in
            mk_term op bterms

   and generalize_term_list state l =
      List.map (generalize_term state) l

   and generalize_bterm state bt =
      let { bvars = bvars; bterm = t } = dest_bterm bt in
      let t = generalize_term state t in
         mk_bterm bvars t

   and generalize_bterm_list state btl =
      List.map (generalize_bterm state) btl

   (* Add additional subscripts to so-vars *)
   and generalize_so_var_term state t =
      let y, cs, ts = dest_so_var t in
      let ts = generalize_term_list state ts in
         match mode, state with
            LeftMode, FinalState
          | RightMode, FinalState ->
               (match replace_context3 cs v vsrc vdst cv1 cv2 with
                   Some cs ->
                      mk_so_var_term (SymbolTable.find info y) cs (x_t :: ts)
                 | None ->
                      mk_so_var_term y cs ts)
          | BaseMode, FinalState
          | FinalMode, FinalState ->
               mk_so_var_term y cs ts
          | _, StartState
          | _, SrcState
          | _, DstState ->
               if mem_context3 cs v vsrc vdst then
                  raise (RefineError ("Meta_context_ind1.generalize_term", StringTermError ("illegal context dependency", t)));
               mk_so_var_term y cs ts

   (* Add additional subscripts to contexts *)
   and generalize_context_term state t =
      let y, t2, cs, ts = dest_context t in
      let t2 = generalize_term state t2 in
      let ts = generalize_term_list state ts in
         match mode, state with
            LeftMode, FinalState
          | RightMode, FinalState ->
               (match replace_context3 cs v vsrc vdst cv1 cv2 with
                   Some cs ->
                      mk_context_term (SymbolTable.find info y) t2 cs (x_t :: ts)
                 | None ->
                      mk_context_term y t2 cs ts)
          | BaseMode, FinalState
          | FinalMode, FinalState ->
               mk_context_term y t2 cs ts
          | _, StartState
          | _, SrcState
          | _, DstState ->
               if mem_context3 cs v vsrc vdst then
                  raise (RefineError ("Meta_context_ind1.generalize_term", StringTermError ("illegal context dependency", t)));
               mk_context_term y t2 cs ts

   (* Analyze sequents *)
   and generalize_sequent_term state t =
      let { sequent_args = arg;
            sequent_hyps = hyps;
            sequent_concl = concl
          } = explode_sequent t
      in
      let arg = generalize_term state arg in
      let state, hyps =
         SeqHyp.fold (fun (state, hyps) _ h ->
               match h with
                  Hypothesis (y, h) ->
                     let h = Hypothesis (y, generalize_term state h) in
                        state, h :: hyps
                | Context (y, cs, ts) ->
                     let ts = generalize_term_list state ts in
                     let var_mode = context_var_mode y vsrc vdst in
                     let hyps =
                        match var_mode, mode, state with
                           (* erase *)
                           SrcVar, BaseMode, _
                         | DstVar, FinalMode, _ ->
                              hyps

                           (* original context *)
                         | SrcVar, FinalMode, _
                         | DstVar, BaseMode, _ ->
                              Context (v, remove_context_vars cs vsrc vdst, ts) :: hyps

                           (* context 1 *)
                         | SrcVar, RightMode, StartState
                         | DstVar, LeftMode, StartState ->
                              Context (cv1, cs, ts) :: hyps

                           (* context 2 *)
                         | SrcVar, RightMode, DstState
                         | DstVar, LeftMode, SrcState ->
                              let cs = replace_var2 cs vsrc vdst cv1 in
                                 Context (cv2, cs, x_t :: ts) :: hyps

                           (* context 1, var *)
                         | SrcVar, LeftMode, StartState
                         | DstVar, RightMode, StartState ->
                              let t_A = mk_so_var_term x_A (cv1 :: cs) [] in
                                 Hypothesis (x, t_A) :: Context (cv1, cs, ts) :: hyps

                           (* var, context 2 *)
                         | SrcVar, LeftMode, DstState
                         | DstVar, RightMode, SrcState ->
                              let cs = replace_var2 cs vsrc vdst cv1 in
                              let t_A = mk_so_var_term x_A cs [] in
                                 Context (cv2, cs, x_t :: ts) :: Hypothesis (x, t_A) :: hyps

                           (* Some other context *)
                         | NoVar, LeftMode, FinalState
                         | NoVar, RightMode, FinalState ->
                              let h =
                                 match replace_context3 cs v vsrc vdst cv1 cv2 with
                                    Some cs ->
                                       Context (SymbolTable.find info y, cs, x_t :: ts)
                                  | None ->
                                       Context (y, cs, ts)
                              in
                                 h :: hyps
                         | NoVar, BaseMode, FinalState
                         | NoVar, FinalMode, FinalState ->
                              Context (y, cs, ts) :: hyps
                         | NoVar, _, StartState
                         | NoVar, _, SrcState
                         | NoVar, _, DstState ->
                              if mem_context3 cs v vsrc vdst then
                                 raise (RefineError ("Meta_context_ind1.generalize_term", StringTermError ("illegal context dependency", t)));
                              Context (y, cs, ts) :: hyps

                           (* Errors *)
                         | SrcVar, _, SrcState
                         | DstVar, _, DstState
                         | SrcVar, _, FinalState
                         | DstVar, _, FinalState ->
                              raise (RefineError ("Meta_context_ind1.generalize_term", StringTermError ("repeated context var", t)))
                     in
                        state_trans state var_mode, hyps) (state, []) hyps
      in
      let concl = generalize_term state concl in
      let seq =
         { sequent_args = arg;
           sequent_hyps = SeqHyp.of_list (List.rev hyps);
           sequent_concl = concl
         }
      in
         mk_sequent_term seq
   in
      generalize_term StartState t

(*
 * Standardize table for the term.
 * Construct a table of new names for variables in case we need them.
 *)
let new_vars_table t =
   let info = all_vars_info SymbolTable.empty t in
   let fv = SymbolTable.fold (fun fv v _ -> SymbolSet.add fv v) SymbolSet.empty info in
      SymbolTable.fold (fun (fv, vars) v info ->
            match info with
               ParamVar
             | FirstOrderVar ->
                  fv, vars
             | ContextVar _
             | SecondOrderVar _
             | SequentContextVar _ ->
                  let v' = maybe_new_var_set v fv in
                  let vars = SymbolTable.add vars v v' in
                  let fv = SymbolSet.add fv v' in
                     fv, vars) (fv, SymbolTable.empty) info

(*
 * All the variables.
 *)
let v_src = Lm_symbol.add "src"
let v_dst = Lm_symbol.add "dst"
let v_x = Lm_symbol.add "x"
let v_A = Lm_symbol.add "A"
let v_S = Lm_symbol.add "S"
let v_T = Lm_symbol.add "T"

let generalize_of_term v t =
   let fv, info = new_vars_table t in

   (* We want to allow these to be passed on the command line *)
   let vsrc = v_src in
   let vdst = v_dst in

   (* Induction vars *)
   let x = maybe_new_var_set v_x fv in
   let fv = SymbolSet.add fv x in

   let cv1 = maybe_new_var_set v_S fv in
   let fv = SymbolSet.add fv cv1 in

   let x_A = maybe_new_var_set v_A fv in
   let fv = SymbolSet.add fv x_A in

   let cv2 = maybe_new_var_set v_T fv in
      generalize_term t v vsrc vdst cv1 x x_A cv2 info

(************************************************************************
 * Context induction.
 *)
let context_ind_extract addrs params goal subgoals args rest =
   raise (Invalid_argument "context_ind_extract: not implemented")

let context_ind_code addrs params goal assums =
   let t_v, t_step =
      match params with
         [t_v; t_step] ->
            t_v, t_step
       | _ ->
            raise (RefineError ("Meta_context_ind1", StringError "context_ind_code requires two arguments"))
   in
   let v = context_var_of_sequent t_v in
   let gen = generalize_of_term v t_step in

   (* Base case *)
   let seq_base = mk_msequent (gen BaseMode) assums in

   (* Step case *)
   let left = gen LeftMode in
   let right = gen RightMode in
   let seq_step = mk_msequent right (assums @ [left]) in

   (* Final case -- we don't require an exact match *)
   let seq_final = mk_msequent goal (assums @ [gen FinalMode]) in
      [seq_base; seq_step; seq_final], context_ind_extract

ml_rule context_ind 't_v 't_step : 'T =
   context_ind_code

let contextIndT t_v t_step =
   context_ind t_v t_step
   thenLT [addHiddenLabelT "base";
           addHiddenLabelT "step";
           addHiddenLabelT "main"]

(************************************************************************
 * Variation: push the context in by a number of turnstiles.
 *)
let rec push_term i c t =
   if is_var_term t then
      t
   else if is_so_var_term t then
      push_so_var_term i c t
   else if is_context_term t then
      push_context_term i c t
   else if is_sequent_term t then
      push_sequent_term i c t
   else
      let { term_op = op; term_terms = bterms } = dest_term t in
      let bterms = push_bterm_list i c bterms in
         mk_term op bterms

and push_so_var_term i c t =
   let x, cs, ts = dest_so_var t in
   let ts = push_term_list i c ts in
      mk_so_var_term x cs ts

and push_context_term i c t =
   let x, t, cs, ts = dest_context t in
   let t = push_term i c t in
   let ts = push_term_list i c ts in
      mk_context_term x t cs ts

and push_sequent_term i c t =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in
   let hyps, concl =
      if i = 0 then
         let cs, ts = c in
         let hyps = SeqHyp.of_list (Context (v_dst, cs, ts) :: SeqHyp.to_list hyps) in
            hyps, concl
      else
         hyps, push_term (pred i) c concl
   in
   let seq =
      { sequent_args = arg;
        sequent_hyps = hyps;
        sequent_concl = concl
      }
   in
      mk_sequent_term seq

and push_term_list i c tl =
   List.map (push_term i c) tl

and push_bterm i c bt =
   let { bvars = vars; bterm = t } = dest_bterm bt in
   let t = push_term i c t in
      mk_bterm vars t

and push_bterm_list i c btl =
   List.map (push_bterm i c) btl

(*
 * Search for a term to push.
 *)
let rec search_push_term v i t =
   if is_var_term t then
      t
   else if is_so_var_term t then
      search_push_so_var_term v i t
   else if is_context_term t then
      search_push_context_term v i t
   else if is_sequent_term t then
      search_push_sequent_term v i t
   else
      let { term_op = op; term_terms = bterms } = dest_term t in
      let bterms = search_push_bterm_list v i bterms in
         mk_term op bterms

and search_push_so_var_term v i t =
   let x, cs, ts = dest_so_var t in
   let ts = search_push_term_list v i ts in
      mk_so_var_term x cs ts

and search_push_context_term v i t =
   let x, t, cs, ts = dest_context t in
   let t = search_push_term v i t in
   let ts = search_push_term_list v i ts in
      mk_context_term x t cs ts

and search_push_sequent_term v i t =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in
   let arg = search_push_term v i arg in
   let hyps, concl = search_push_hyps v i (SeqHyp.to_list hyps) concl in
   let seq =
      { sequent_args = arg;
        sequent_hyps = SeqHyp.of_list hyps;
        sequent_concl = concl
      }
   in
      mk_sequent_term seq

and search_push_hyps v i hyps concl =
   match hyps with
      h :: hyps ->
         (match h with
             Hypothesis (x, t) ->
                let hyps, concl = search_push_hyps v i hyps concl in
                let hyps = Hypothesis (x, search_push_term v i t) :: hyps in
                   hyps, concl
           | Context (x, cs, ts) ->
                let ts = search_push_term_list v i ts in
                   if Lm_symbol.eq x v then
                      let concl = push_term i (v_src :: cs, ts) concl in
                         Context (v_src, cs, ts) :: hyps, concl
                   else
                      let hyps, concl = search_push_hyps v i hyps concl in
                         Context (x, cs, ts) :: hyps, concl)
    | [] ->
         let concl = search_push_term v i concl in
            [], concl

and search_push_term_list v i tl =
   List.map (search_push_term v i) tl

and search_push_bterm v i bt =
   let { bvars = vars; bterm = t } = dest_bterm bt in
   let t = search_push_term v i t in
      mk_bterm vars t

and search_push_bterm_list v i btl =
   List.map (search_push_bterm v i) btl

(*
 * Push the context in one turnstile.
 *)
let context_push_ind t_v i p =
   let v = context_var_of_sequent t_v in
   let t_step = search_push_term v i (Sequent.goal p) in
      contextIndT t_v t_step

let contextPushIndT t_v i =
   funT (context_push_ind t_v i)

(************************************************************************
 * Variation: hoist the context by some number of turnstiles.
 *)

(*
 * Hoist checks require that the depth match.
 *)
let check_hoist2 hoist1 hoist2 =
   match hoist1, hoist2 with
      (Some _ as hoist), None
    | None, (Some _ as hoist) ->
         hoist
    | None, None ->
         None
    | Some (i1, _, _), Some (i2, _, _) ->
         if i1 = i2 then
            hoist1
         else
            raise (RefineError ("Meta_context_ind1", StringError "check_hoist2: hoist depth mismatch"))

let check_hoist3 hoist1 hoist2 hoist3 =
   check_hoist2 (check_hoist2 hoist1 hoist2) hoist3

(*
 * Search for a term to push.
 *)
let rec search_hoist_term v i t =
   if is_var_term t then
      None, t
   else if is_so_var_term t then
      search_hoist_so_var_term v i t
   else if is_context_term t then
      search_hoist_context_term v i t
   else if is_sequent_term t then
      search_hoist_sequent_term v i t
   else
      let { term_op = op; term_terms = bterms } = dest_term t in
      let hoist, bterms = search_hoist_bterm_list v i bterms in
         hoist, mk_term op bterms

and search_hoist_so_var_term v i t =
   let x, cs, ts = dest_so_var t in
   let hoist, ts = search_hoist_term_list v i ts in
      hoist, mk_so_var_term x cs ts

and search_hoist_context_term v i t =
   let x, t, cs, ts = dest_context t in
   let hoist1, t = search_hoist_term v i t in
   let hoist2, ts = search_hoist_term_list v i ts in
   let hoist = check_hoist2 hoist1 hoist2 in
      hoist, mk_context_term x t cs ts

and search_hoist_sequent_term v i t =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in
   let hoist1, arg = search_hoist_term v i arg in
   let hoist2, hyps = search_hoist_hyps v i (SeqHyp.to_list hyps) in
   let hoist3, concl = search_hoist_term v i concl in
   let hoist3, hyps =
      match hoist3 with
         Some (0, cs, ts) ->
            None, hyps @ [Context (v_dst, cs, ts)]
       | Some (i, cs, ts) ->
            Some (pred i, cs, ts), hyps
       | None ->
            None, hyps
   in
   let hoist = check_hoist3 hoist1 hoist2 hoist3 in
   let seq =
      { sequent_args = arg;
        sequent_hyps = SeqHyp.of_list hyps;
        sequent_concl = concl
      }
   in
      hoist, mk_sequent_term seq

and search_hoist_hyps v i = function
   [] ->
      None, []
 | h :: hyps ->
      match h with
         Hypothesis (x, t) ->
            let hoist1, t = search_hoist_term v i t in
            let hoist2, hyps = search_hoist_hyps v i hyps in
            let hoist2, hyps =
               match hoist2 with
                  Some (0, cs, ts) ->
                     None, Context (v_dst, cs, ts) :: Hypothesis (x, t) :: hyps
                | Some (i, cs, ts) ->
                     Some (pred i, cs, ts), Hypothesis (x, t) :: hyps
                | None ->
                     None, Hypothesis (x, t) :: hyps
            in
            let hoist = check_hoist2 hoist1 hoist2 in
               hoist, hyps
       | Context (x, cs, ts) ->
            let hoist1, ts = search_hoist_term_list v i ts in
            let hoist2, hyps = search_hoist_hyps v i hyps in
            let hoist3, hyps =
               if Lm_symbol.eq x v then
                  Some (i, cs, ts), Context (v_src, v_dst :: cs, ts) :: hyps
               else
                  None, Context (x, cs, ts) :: hyps
            in
            let hoist = check_hoist3 hoist1 hoist2 hoist3 in
               hoist, hyps

and search_hoist_term_list v i tl =
   let hoist, tl =
      List.fold_left (fun (hoist1, tl) t ->
            let hoist2, t = search_hoist_term v i t in
            let hoist = check_hoist2 hoist1 hoist2 in
               hoist, t :: tl) (None, []) tl
   in
      hoist, List.rev tl

and search_hoist_bterm v i bt =
   let { bvars = vars; bterm = t } = dest_bterm bt in
   let hoist, t = search_hoist_term v i t in
      hoist, mk_bterm vars t

and search_hoist_bterm_list v i btl =
   let hoist, btl =
      List.fold_left (fun (hoist1, btl) bt ->
            let hoist2, bt = search_hoist_bterm v i bt in
            let hoist = check_hoist2 hoist1 hoist2 in
               hoist, bt :: btl) (None, []) btl
   in
      hoist, List.rev btl

(*
 * Push the context in one turnstile.
 *)
let context_hoist_ind t_v i p =
   let v = context_var_of_sequent t_v in
   let _, t_step = search_hoist_term v i (Sequent.goal p) in
      contextIndT t_v t_step

let contextHoistIndT t_v i =
   funT (context_hoist_ind t_v i)

(************************************************************************
 * Testing.
 *)

(*
 * Simple test.
 *)
declare sequent [test] { Term : Term >- Term } : Term

interactive test1 'S :
   sequent { <H> >- 'S } -->
   sequent { <H> >- test{| <J> >- 'C |} }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
