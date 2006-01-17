doc <:doc<
   @module[Dtactic]

   The @tactic[meta_dT] tactic is the analog of @tactic[dT], but
   for the meta-logic.

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998-2005 Mojave Group, Caltech

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
   Modified by: Aleksey Nogin @email{nogin@cs.cornell.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Base_theory
doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics
open Simple_print

open Browser_resource

let debug_meta_dtactic =
   create_debug (**)
      { debug_name = "meta_dtactic";
        debug_description = "display meta_dT tactic operations";
        debug_value = false
      }

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Extract a D tactic from the data.
 * The tactic checks for an optable.
 *)
let extract_elim_data =
   let select_options options (opts, _) =
      match opts with
         None ->
            true
       | Some opts ->
            options_are_allowed options opts
   in
   let rec firstiT i = function
      [] ->
         raise (Invalid_argument "extract_elim_data: internal error")
    | [_, tac] ->
         tac i
    | (_, tac) :: tacs ->
         tac i orelseT firstiT i tacs
   in
      (fun tbl ->
            argfunT (fun i p ->
                  let t = Sequent.nth_assum p i in
                  let options = get_options p in
                  let () =
                     if !debug_meta_dtactic then
                        eprintf "meta_d_tactic: elim: lookup %s%t" (SimplePrint.short_string_of_term t) eflush
                  in
                  let tacs =
                     try
                        lookup_bucket tbl (select_options options) t
                     with
                        Not_found ->
                           raise (RefineError ("extract_elim_data", StringTermError ("D tactic doesn't know about", t)))
                  in
                     firstiT i tacs))

let in_auto p =
   match Sequent.get_int_arg p "d_auto" with
      Some 0
    | Some 1 ->
         true
    | _ ->
         false

let extract_intro_data =
   let select_intro p in_auto_type (_, sel, options, auto_type, _) =
      (match in_auto_type, auto_type with
          Some 0, AutoTrivial
        | Some 1, AutoNormal
        | Some 2, AutoComplete
        | None, _ ->
             true
        | _ ->
             false)
      &&
      (match sel with
          None ->
             true
        | Some i ->
             match get_sel_arg p with
                 Some i' ->
                    i' = i
               | None ->
                    false)
      &&
      (match options with
          None ->
             true
        | Some opts ->
             options_are_allowed_arg p opts)
   in
   let extract (name, _, _, _, tac) =
      if !debug_meta_dtactic then
         eprintf "meta_d_tactic: intro: found %s%t" name eflush; tac
   in
      (fun tbl ->
            funT (fun p ->
                  let t = Sequent.goal p in
                  let () =
                     if !debug_meta_dtactic then
                        eprintf "meta_d_tactic: intro: lookup %s%t" (SimplePrint.short_string_of_term t) eflush
                  in
                  let tacs =
                     try lookup_bucket tbl (select_intro p (Sequent.get_int_arg p "d_auto")) t with
                        Not_found ->
                           let msg =
                              match get_sel_arg p with
                                 Some _ ->
                                    "meta_dT tactic failed: the select argument may be out of range"
                               | None ->
                                    "meta_dT tactic failed: the rule may not apply, or option arguments may not be valid"
                           in
                              raise (RefineError ("extract_intro_data", StringTermError (msg, t)))
                  in
                     firstT (List.map extract tacs)))

(*
 * Options for intro rule.
 *)
let rec get_args_arg = function
   IntroArgsOption (f, arg) :: t ->
      Some (f, arg)
 | _ :: t ->
      get_args_arg t
 | [] ->
      None

let rec get_sel_arg = function
   SelectOption sel :: t ->
      Some sel
 | _ :: t ->
      get_sel_arg t
 | [] ->
      None

let one_rw_arg i =
   { arg_ints = [| i |]; arg_addrs = [||] }

(*
 * Improve the intro resource from a rule.
 *)
let process_meta_intro_resource_annotation ?(options = []) ?select name args term_args statement loc pre_tactic =
   if args.spec_addrs <> [||] then
      raise (Invalid_argument (sprintf
         "%s: intro annotation: %s: context arguments not supported yet" (string_of_loc loc) name));
   let assums, goal = unzip_mfunction statement in
   let goal = TermMan.explode_sequent goal in
   let t = goal.sequent_concl in
   let term_args_fun =
      match term_args with
         [] ->
            (fun _ -> [])
       | _ ->
            match get_args_arg options with
               Some (f, arg) ->
                  let get_arg =
                     match arg with
                        None ->
                           Sequent.concl
                      | Some arg ->
                        begin match find_subterm t (fun t _ -> alpha_equal t arg) with
                                 addr :: _ ->
                                    (fun p -> term_subterm (Sequent.concl p) addr)
                               | [] ->
                                    raise (RefineError("intro annotation",
                                                       StringTermError("term not found in the conclusion", arg)))
                        end
                  in
                     (fun p -> f p (get_arg p))
             | None ->
                  let length = List.length term_args in
                     (fun p ->
                           let args =
                              try get_with_args p with
                                 RefineError _ ->
                                    raise (RefineError (name, StringIntError ("arguments required", length)))
                           in
                           let length' = List.length args in
                              if length' != length then
                                 raise (RefineError (name, StringIntError ("wrong number of arguments", length')));
                              args)
   in
   let tac =
      match args.spec_ints, SeqHyp.to_list goal.sequent_hyps with
         [||], [Context _] ->
            if term_args = [] then  (* optimization *)
               Tactic_type.Tactic.tactic_of_rule pre_tactic empty_rw_args []
            else
               funT (fun p -> Tactic_type.Tactic.tactic_of_rule pre_tactic empty_rw_args (term_args_fun p))
       | [|_|], [Context _; Hypothesis _; Context _] when not (is_so_var_term t) ->
            onSomeHypT (argfunT (fun i p -> Tactic_type.Tactic.tactic_of_rule pre_tactic (one_rw_arg i) (term_args_fun p)))
       | _ ->
            raise (Invalid_argument (sprintf "meta_d_tactic.intro: %s: not an introduction rule" name))
   in
   let sel_opts = get_sel_arg options in
   let option_opts = opset_of_opt_terms select in
   let rec auto_aux = function
      [] ->
         [t, (name, sel_opts, option_opts, (if assums = [] then AutoTrivial else AutoNormal), tac)]
    | AutoMustComplete :: _ ->
         [t, (name, sel_opts, option_opts, AutoComplete, tac)]
    | CondMustComplete f :: _ ->
         let auto_exn = RefineError ("intro_annotation: " ^ name, StringError "not appropriate in weakAutoT") in
         let tac' =
            funT (fun p -> if f p then raise auto_exn else tac)
         in
            [t, (name, sel_opts, option_opts, AutoNormal, tac');
             t, (name, sel_opts, option_opts, AutoComplete, tac)]
    | _ :: tl ->
         auto_aux tl
   in
      auto_aux options

(*
 * Compile an elimination tactic.
 *)
let rec get_elim_args_arg = function
   ElimArgsOption (f, arg) :: t ->
      Some (f, arg)
 | _ :: t ->
      get_elim_args_arg t
 | [] ->
      None

let process_meta_elim_resource_annotation ?(options = []) ?select name args term_args statement loc pre_tactic =
   if args.spec_addrs <> [||] then
      raise (Invalid_argument (sprintf
         "%s: elim annotation: %s: context arguments not supported yet" (string_of_loc loc) name));
   let assums, goal = unzip_mfunction statement in
   match SeqHyp.to_list (TermMan.explode_sequent goal).sequent_hyps with
      [ Context _; Hypothesis(v,t); Context _ ] ->
         let term_args =
            match term_args with
               [] ->
                  (fun _ _ -> [])
             | _ ->
                  match get_elim_args_arg options with
                     Some (f, arg) ->
                        let get_arg =
                           match arg with
                              None ->
                                 (fun p i -> Sequent.nth_assum p i)
                            | Some arg ->
                                 begin match find_subterm t (fun t _ -> alpha_equal t arg) with
                                    addr :: _ ->
                                       (fun p i -> term_subterm (Sequent.nth_assum p i) addr)
                                 | [] ->
                                       raise (RefineError("intro annotation",
                                          StringTermError("term not found in the conclusion", arg)))
                                 end
                        in
                           (fun i p -> f p (get_arg p i))
                   | None ->
                        let length = List.length term_args in
                           (fun _ p ->
                                 let args =
                                    try get_with_args p with
                                       RefineError _ ->
                                          raise (RefineError (name, StringIntError ("arguments required", length)))
                                 in
                                 let length' = List.length args in
                                    if length' != length then
                                       raise (RefineError (name, StringIntError ("wrong number of arguments", length')));
                                    args)
         in
         let thinT =
            let rec collect = function
               ThinOption thinT :: _ ->
                  Some thinT
             | _ :: t ->
                  collect t
             | [] ->
                  None
            in
               collect options
         in
         let tac =
            match args.spec_ints, thinT with
               [| _ |], None ->
                  argfunT (fun i p ->
                     if !debug_meta_dtactic then
                        eprintf "dT elim: trying %s%t" name eflush;
                     Tactic_type.Tactic.tactic_of_rule pre_tactic (one_rw_arg i) (term_args i p))

             | [| _ |], Some thinT ->
                  let rec find_thin_num_aux hyps len i =
                     if i = len then
                        raise (Invalid_argument (sprintf "meta_d_tactic.improve_elim: %s: can not find what to thin in one of the subgoals" name));
                     match SeqHyp.get hyps i with
                        Hypothesis (_, t') when alpha_equal t t' -> i
                      | Hypothesis (v', _) when Lm_symbol.eq v v' -> i
                      | _ -> find_thin_num_aux hyps len (succ i)
                  in
                  let find_thin_num (_,_,assum) =
                     try
                        let hyps = (TermMan.explode_sequent assum).sequent_hyps in
                        find_thin_num_aux hyps (SeqHyp.length hyps) 0
                     with RefineError _ ->
                        raise (Invalid_argument (sprintf "meta_d_tactic.improve_elim: %s: assumptions must be sequents" name))
                  in
                  let thin_nums = List.map find_thin_num assums in
                  let rec check_thin_nums = function
                     [i] -> i
                   | i :: ((i'::_) as tl) when (i=i') -> check_thin_nums tl
                   | [] ->
                        raise (Invalid_argument (sprintf "meta_d_tactic.improve_elim: %s: should not use ThinOption in a rule with no assumptions" name))
                   | _ -> raise (Invalid_argument (sprintf "meta_d_tactic.improve_elim: %s: ThinOption: different assumptions have the eliminated hypothesis in a different place" name))
                  in
                  let thin_incr = (check_thin_nums thin_nums) - 1 in
                  argfunT (fun i p ->
                     if !debug_meta_dtactic then
                        eprintf "dT elim: trying %s%t" name eflush;
                     let tac = Tactic_type.Tactic.tactic_of_rule pre_tactic (one_rw_arg i) (term_args i p)
                     in
                        if get_thinning_arg p then
                           tac thenT tryT (thinT (i + thin_incr))
                        else
                           tac)
             | _ ->
                  raise (Invalid_argument (sprintf "meta_d_tactic: %s: not an elimination rule" name))
         in
         let opts = opset_of_opt_terms select in
            [t, (opts, tac)]
    | _ ->
         raise (Invalid_argument (sprintf "meta_d_tactic.improve_elim: %s: must be an elimination rule" name))

(*
 * Resources
 *)
let resource (term * elim_item, int -> tactic) meta_elim =
   table_resource_info extract_elim_data

let resource (term * intro_item, tactic) meta_intro =
   table_resource_info extract_intro_data

let meta_dT =
   argfunT (fun i p ->
         if i = 0 then
            Sequent.get_resource_arg p get_meta_intro_resource
         else
            Sequent.get_resource_arg p get_meta_elim_resource (Sequent.get_pos_assum_num p i))

let rec meta_dForT i =
   if i <= 0 then
      idT
   else
      dT 0 thenMT dForT (pred i)

(*
 * By default, dT 0 should always make progress.
 *)
let d_prec = create_auto_prec [trivial_prec] [nth_hyp_prec]
let d_elim_prec = create_auto_prec [trivial_prec; d_prec] [reduce_prec]

let eq_exn = RefineError ("meta_dT", StringError "elim rule not suitable for autoT")

let rec num_equal_aux t hyps i =
   if i <= 0 then 0 else
   let i = pred i in
      (num_equal_aux t hyps i) +
      match SeqHyp.get hyps i with
         Hypothesis (_, t') when alpha_equal t t' -> 1
       | _ -> 0

let num_equal t p =
   let hyps = (TermMan.explode_sequent (Sequent.goal p)).sequent_hyps in
      num_equal_aux t hyps (SeqHyp.length hyps)

let check_num_equalT n t = funT (fun p ->
   if num_equal t p >= n then raise eq_exn else idT)

(*
let auto_dT =
   argfunT (fun i p ->
      let t = Sequent.nth_assum p i in
         meta_dT i thenT check_num_equalT (num_equal t p) t)

let resource auto += [ {
   auto_name = "meta_dT trivial";
   auto_prec = d_prec;
   auto_tac = withIntT "d_auto" 0 (dT 0);
   auto_type = AutoTrivial;
}; {
   auto_name = "meta_dT";
   auto_prec = d_prec;
   auto_tac = withIntT "d_auto" 1 (dT 0);
   auto_type = AutoNormal;
}; {
   auto_name = "meta_dT complete";
   auto_prec = d_prec;
   auto_tac = withIntT "d_auto" 2 (dT 0);
   auto_type = AutoComplete;
}; {
   auto_name = "meta_dT elim-complete";
   auto_prec = d_elim_prec;
   auto_tac = onSomeHypT auto_dT;
   auto_type = AutoComplete;
}]
 *)

(*
 * Add meta_dT 0 to the browser.
 *)
let resource menubar +=
    [<< menuitem["refine", "dT 0", "Command('refine meta_dT 0')"] >>, refine_is_enabled]

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)

