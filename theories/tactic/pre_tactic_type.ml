(*
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

open Mp_debug
open Printf
open Thread_util

open Opname
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Refiner.Refiner.Refine

open Theory

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Tactic_type%t" eflush

let debug_tactic =
   create_debug (**)
      { debug_name = "tactic";
        debug_description = "display primitive tactic operations";
        debug_value = false
      }

let debug_refine = load_debug "refine"

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(************************************************************************
 * Definitions needed before the ThreadRefiner can be instantiated.
 *)

(*
 * An extract has these kinds:
 *   + A goal term without any justification
 *   + A step that is unjustified
 *   + A raw refine extract, saving the number of subgoals
 *   + A composition of extracts
 *   + An annotated extract
 *   + A rule box, which is a combined annotation/composition
 *
 * 'info is the type of proof annotations provided by tactics
 * 'arg represents a goal term (a tactic_arg)
 *)
type ('info, 'arg) pre_extract =
   Goal of 'arg
 | Unjustified of 'arg * 'arg list
 | Extract of Refine.extract * int
 | Compose of ('info, 'arg) pre_extract * ('info, 'arg) pre_extract list
 | Wrapped of 'info * ('info, 'arg) pre_extract
 | RuleBox of ('info, 'arg) pre_rule_info
 | Identity

and ('info, 'arg) pre_rule_info =
   { rule_info : 'info;
     rule_extract : ('info, 'arg) pre_extract;
     rule_subgoals : ('info, 'arg) pre_extract list;
     rule_extras : ('info, 'arg) pre_extract list
   }

(************************************************************************
 * Instantiate the ThreadRefiner.
 *)
module ThreadRefinerArg =
struct
   type ('info, 'arg) extract = ('info, 'arg) pre_extract
   let identity = Identity
   let compose ext extl = Compose (ext, extl)
end

module ThreadRefinerTacticals = Thread_refiner.ThreadRefinerTacticals
module ThreadRefinerAux = Thread_refiner.MakeThreadRefiner (ThreadRefinerArg)

(*
 * We have to create explicit function points to get the marshaler to
 * work correctly (Without marshaling the entire ThreadRefiner).
 *)
module ThreadRefiner =
struct
   let arg_of_key = ThreadRefinerAux.arg_of_key
   let share = ThreadRefinerAux.share
   let create_value = ThreadRefinerAux.create_value
end

(************************************************************************
 * Now define the usual types.
 *
 * A tactic argument (goal) has the following:
 *   ref_goal: the goal term
 *   ref_label: a string that labels the particular kind of goal
 *   ref_arg: changeable attributes
 *   ref_static: a key to the static attributes
 *   ref_cache: a ket to the refinement cache
 *   ref_sentinal: a key to the refiner sentinal
 *)
type ('info, 'arg, 'static) tactic_arg =
   { ref_goal : msequent;
     ref_label : string;
     ref_arg : 'arg;
     ref_static : 'static ThreadRefinerAux.key;
     ref_cache : ('info, 'arg, 'static) tactic Tactic_cache.extract ThreadRefinerAux.key;
     ref_sentinal : Refine.sentinal ThreadRefinerAux.key
   }

and ('info, 'arg, 'static) extract =
   ('info, ('info, 'arg, 'static) tactic_arg) pre_extract

and ('info, 'arg, 'static) rule_info =
   ('info, ('info, 'arg, 'static) tactic_arg) pre_rule_info

(*
 * A tactic_value is the value produced by the ThreadRefiner,
 * which gives an "eval" method for producing the extract.
 *)
and pre_tactic   = prim_tactic
and ('info, 'arg, 'static) tactic_value = ('info, 'arg, ('info, 'arg, 'static) tactic_arg) ThreadRefinerAux.t
and ('info, 'arg, 'static) tactic       = ('info, 'arg, 'static) tactic_arg -> ('info, 'arg, 'static) tactic_value

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Server is created at file execution time.
 *)
let print_tactic_arg out { ref_goal = goal } =
   let goal, _ = dest_msequent goal in
   let goal = TermMan.nth_concl goal 0 in
      debug_print out goal

let args = ThreadRefinerAux.args

let remote_server = (* Register.set 0 *) (ThreadRefinerAux.create print_tactic_arg)

let get_remote_server () =
   (* Register.get *) remote_server

(*
 * Create an initial tactic_arg for a proof.
 * Cache is initially out-of-date.  It will be
 * set to the current goal when requested.
 *)
let create sentinal label goal cache arg static =
   { ref_goal = goal;
     ref_label = label;
     ref_arg = arg;
     ref_static = ThreadRefinerAux.share static;
     ref_cache = ThreadRefinerAux.share cache;
     ref_sentinal = ThreadRefineAux.share sentinal
   }

let main_loop () =
   ThreadRefinerAux.main_loop (get_remote_server ())

(*
 * Access to the sequent.
 *)
let msequent { ref_goal = seq } =
   seq

let goal { ref_goal = goal } =
   fst (dest_msequent goal)

let nth_hyp { ref_goal = goal } i =
   TermMan.nth_hyp (fst (dest_msequent goal)) i

let nth_concl { ref_goal = goal } i =
   TermMan.nth_concl (fst (dest_msequent goal)) i

let label { ref_label = label } =
   label

(*
 * Modify the argument.
 *)
let set_goal arg goal =
   let { ref_goal = seq;
         ref_label = label;
         ref_arg = arg;
         ref_static = static;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = arg
   in
      { ref_goal = mk_msequent goal (snd (dest_msequent seq));
        ref_label = label;
        ref_arg = arg;
        ref_static = static;
        ref_cache = cache;
        ref_sentinal = sentinal
      }

let set_concl arg concl =
   let { ref_goal = seq;
         ref_label = label;
         ref_arg = arg;
         ref_static = static;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = arg
   in
   let goal, hyps = dest_msequent seq in
      { ref_goal = mk_msequent (replace_goal goal concl) hyps;
        ref_label = label;
        ref_arg = arg;
        ref_static = static;
        ref_cache = cache;
        ref_sentinal = sentinal
      }

let set_label arg label =
   let { ref_goal = goal;
         ref_arg = arg;
         ref_static = static;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = arg
   in
      { ref_goal = goal;
        ref_label = label;
        ref_arg = arg;
        ref_static = static;
        ref_cache = cache;
        ref_sentinal = sentinal
      }

(************************************************************************
 * SENTINAL                                                             *
 ************************************************************************)

(*
 * Sentinal function is lazy.
 *)
let get_theory name =
   let rec search = function
      thy :: t ->
         if thy.thy_name = name then
            thy
         else
            search t
    | [] ->
         raise (RefineError ("get_theory", StringStringError ("theory is not found", name)))
   in
      search (get_theories ())

let sentinal_of_refiner mod_name name =
   let xlazy () =
      let refiner = (get_theory mod_name).thy_refiner in
      let opname = make_opname [name; mod_name] in
      let refiner =
         try snd (dest_refiner (find_refiner refiner opname)) with
            Not_found ->
               eprintf "Warning: using default refiner for %s%t" name eflush;
               refiner
      in
         Refine.sentinal_of_refiner refiner
   in
      ThreadRefiner.share (get_remote_server ()) "sentinal_object" xlazy

let get_sentinal key =
   ThreadRefiner.arg_of_key (get_remote_server ()) key

(************************************************************************
 * CACHE                                                                *
 ************************************************************************)

(*
 * Cache function is lazy.
 *)
let make_cache f =
   ThreadRefiner.share (get_remote_server ()) "cache" (fun () -> (ref (OutOfDate (f ()))))

(*
 * Caching.
 *)
let cache arg =
   let cache = ThreadRefiner.arg_of_key (get_remote_server ()) arg.ref_cache in
      match !cache with
         Current cache ->
            cache
       | OutOfDate cache' ->
            let cache' = Tactic_cache.set_msequent cache' arg.ref_goal in
               cache := Current cache';
               cache'

let out_of_date key =
   let cache = ThreadRefiner.arg_of_key (get_remote_server ()) key in
      match !cache with
         Current cache' ->
            cache := OutOfDate cache'
       | OutOfDate _ ->
            ()

(************************************************************************
 * REFINEMENT                                                           *
 ************************************************************************)

(*
 * Two args are equal if their goals are equal.
 * Other arguments are ignored.
 *)
let tactic_arg_alpha_equal { ref_goal = goal1 } { ref_goal = goal2 } =
   msequent_alpha_equal goal1 goal2

(*
 * The refiner applies the tactic to the arg.
 * We keep a list of final values that should
 * be evaluated after refinement.  This side-effect
 * is ok if it is used only for outermost refinement.
 * If a remote tactic executes the add_final_hook,
 * it will have no effect.
 *)
let refine_final_list = ref []

let add_final_hook f =
   refine_final_list := f :: !refine_final_list

let refine tac arg =
   refine_final_list := [];
   let x = ThreadRefinerAux.eval (get_remote_server ()) (tac arg) in
      List_util.rev_iter (fun f -> f ()) !refine_final_list;
      refine_final_list := [];
      x

(*
 * Eventually, we may want to look at the rule and do something
 * special here.
 *)
let compile_rule refiner tac =
   tac

(*
 * Utility for reconstructing the subgoals
 * in a tactic application.
 *)
let make_subgoal
    { ref_label = label;
      ref_arg = arg;
      ref_static = static;
      ref_cache = cache;
      ref_sentinal = sentinal
    } goal =
   { ref_goal = goal;
     ref_label = label;
     ref_arg = arg;
     ref_static = static;
     ref_cache = out_of_date cache;
     ref_sentinal = sentinal
   }

(*
 * Construct polymorphic tactic.
 *)
let tactic_of_rule rule (addrs, names) params arg =
   if !debug_tactic then
      let _ = eprintf "Collecting addresses%t" eflush in
      let rule = rule (addrs, names) params in
      let _ = eprintf "Starting refinement%t" eflush in
      let subgoals, ext = Refine.refine (get_sentinal arg.ref_sentinal) rule arg.ref_goal in
         eprintf "tactic_of_rule done%t" eflush;
         ThreadRefinerTacticals.create_value (List.map (make_subgoal arg) subgoals) (Extract (ext, List.length subgoals))
   else
      let rule = rule (addrs, names) params in
      let subgoals, ext = Refine.refine (get_sentinal arg.ref_sentinal) rule arg.ref_goal in
         ThreadRefinerTacticals.create_value (List.map (make_subgoal arg) subgoals) (Extract (ext, List.length subgoals))

(*
 * Construct polymorphic tactic.
 *)
let tactic_of_refine_tactic rule arg =
   let _ =
      if !debug_tactic then
         eprintf "Starting refinement%t" eflush
   in
   let { ref_goal = goal; ref_sentinal = sentinal } = arg in
   let subgoals, ext = Refine.refine (get_sentinal sentinal) rule goal in
      if !debug_tactic then
         eprintf "tactic_of_rule done%t" eflush;
      List.map (make_subgoal arg) subgoals, Extract (ext, List.length subgoals)

(*
 * Convert a rewrite into a tactic.
 *)
let tactic_of_rewrite_exn1 = RefineError ("tactic_of_rewrite", StringError "rewrite did not produce a goal")
let tactic_of_rewrite_exn2 = RefineError ("tactic_of_rewrite", StringError "rewrite produced too many goals")

let tactic_of_rewrite rw arg =
   let rule = rwtactic rw in
   let { ref_goal = goal;
         ref_label = label;
         ref_arg = arg;
         ref_static = static;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = arg
   in
      match Refine.refine (get_sentinal sentinal) rule goal with
         [subgoal], ext ->
            let subgoal =
               { ref_goal = subgoal;
                 ref_label = label;
                 ref_arg = arg;
                 ref_static = static;
                 ref_cache = out_of_date cache;
                 ref_sentinal = sentinal
               }
            in
               ThreadRefinerTacticals.create_value [subgoal] (Extract (ext, 1))
       | [], _ ->
            raise tactic_of_rewrite_exn1
       | _ ->
            raise tactic_of_rewrite_exn2


(*
 * Convert a conditional rewrite to a tactic.
 *)
let tactic_of_cond_rewrite crw arg =
   let rule = crwtactic crw in
   let { ref_goal = goal;
         ref_label = label;
         ref_arg = arg;
         ref_static = static;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = arg
   in
   let subgoals, ext = Refine.refine (get_sentinal sentinal) rule goal in
   let make_subgoal goal =
      { ref_goal = goal;
        ref_label = label;
        ref_arg = arg;
        ref_static = static;
        ref_cache = out_of_date cache;
        ref_sentinal = sentinal
      }
   in
      ThreadRefinerTacticals.create_value (List.map make_subgoal subgoals) (Extract (ext, List.length subgoals))

(************************************************************************
 * EXTRACTS                                                             *
 ************************************************************************)

(*
 * Compose two extracts.
 *)
let compose ext extl =
   Compose (ext, extl)

(*
 * Flatten the extract tree to produce a normal form.
 *)
let justify_identity_exn = RefineError ("Tactic_type.justify", StringError "identity tactic failed")
let justify_incomplete_exn = RefineError ("Tactic_type.justify", StringError "extract is incomplete")

let rec justify extl = function
   Identity ->
      begin
         match extl with
            ext :: extl ->
               ext, extl
          | [] ->
               raise justify_identity_exn
      end

 | Compose (ext, extl') ->
      let rec justify_list extl = function
         ext' :: extl' ->
            let ext', extl = justify extl ext' in
            let extl', extl = justify_list extl extl' in
               ext' :: extl', extl
       | [] ->
            [], extl
      in
      let extl', extl = justify_list extl extl' in
      let ext, _ = justify extl' ext in
         Refine.compose ext extl', extl

 | Extract (ext, n) ->
      let extl, extl' = List_util.split_list n extl in
         Refine.compose ext extl, extl'

 | Wrapped (_, ext) ->
      justify extl ext

 | RuleBox { rule_extract = ext; rule_subgoals = extl' } ->
      justify extl (Compose (ext, extl'))

 | Goal _
 | Unjustified _ ->
      raise justify_incomplete_exn

(*
 * To produce a term from the extract, the proof must be complete.
 *)
let term_of_extract refiner ext args =
   let ext, _ = justify [] ext in
      Refine.term_of_extract refiner ext args

(************************************************************************
 * TACTICALS                                                            *
 ************************************************************************)

(*
 * Assumption tactic from the refiner.
 * Assumptions are numbered from 1, but
 * refiner numbers them from 0.
 *)
let nthAssumT i p =
   let i = pred i in
      if !debug_refine then
         begin
            let { ref_goal = seq } = p in
            let goal, hyps = dest_msequent seq in
               eprintf "Tactic_type.nthAssumT:\nHyp: %d%t" i eflush;
               List.iter (fun hyp ->
                     print_term stderr hyp;
                     eflush stderr) hyps;
               eprintf "\nGoal: ";
               print_term stderr goal;
               eflush stderr
         end;
      let subgoals, ext = tactic_of_refine_tactic (Refine.nth_hyp i) p in
         ThreadRefinerTacticals.create_value subgoals ext

(*
 * Identity doesn't do anything.
 *)
let idT p =
   ThreadRefinerTacticals.create_value [p] Identity

(*
 * Sequencing tactics.
 *)
let prefix_thenT = ThreadRefinerTacticals.compose1
let prefix_thenLT = ThreadRefinerTacticals.compose2
let prefix_thenFLT = ThreadRefinerTacticals.composef
let firstT = ThreadRefinerTacticals.first
let prefix_orelseT tac1 tac2 =
   firstT [tac1; tac2]

(*
 * Modify the label.
 *)
let setLabelT name p =
   let { ref_goal = goal;
         ref_arg = arg;
         ref_static = static;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = p
   in
   let p =
      { ref_goal = goal;
        ref_label = name;
        ref_arg = arg;
        ref_static = static;
        ref_cache = cache;
        ref_sentinal = sentinal
      }
   in
      ThreadRefinerTacticals.create_value [p] Identity

(*
 * Add a term argument.
 *)
let withT arg tac p =
   let make_goal
       { ref_goal = goal;
         ref_label = name;
         ref_static = static;
         ref_cache = cache;
         ref_sentinal = sentinal
       } =
      ThreadRefinerTacticals.create_value  (**)
         [{ ref_goal = goal;
            ref_label = name;
            ref_arg = arg;
            ref_static = static;
            ref_cache = cache;
            ref_sentinal = sentinal
          }] Identity
   in
   let arg' = p.ref_arg in
   let make_subgoal p =
      let { ref_goal = goal;
            ref_label = name;
            ref_static = static;
            ref_cache = cache;
            ref_sentinal = sentinal
          } = p
      in
         ThreadRefinerTacticals.create_value (**)
            [{ ref_goal = goal;
               ref_label = name;
               ref_arg = arg';
               ref_static = static;
               ref_cache = cache;
               ref_sentinal = sentinal
             }]  Identity
   in
      (make_goal thenT tac thenT make_subgoal) p

(*
 * Add a function executed at the end of tactic refinement.
 *)
let finalT f p =
   add_final_hook f;
   idT p

(*
 * Print timing information after the tactic is finished.
 *)
let timingT tac p =
   let start = Unix.times () in
   let start_time = Unix.gettimeofday () in
   let finalize () =
      let finish = Unix.times () in
      let finish_time = Unix.gettimeofday () in
         eprintf "User time %f; System time %f; Real time %f%t" (**)
            ((finish.Unix.tms_utime +. finish.Unix.tms_cutime)
             -. (start.Unix.tms_utime +. start.Unix.tms_cstime))
            ((finish.Unix.tms_stime +. finish.Unix.tms_cstime)
             -. (start.Unix.tms_stime +. finish.Unix.tms_cstime))
            (finish_time -. start_time)
            eflush
   in
      add_final_hook finalize;
      tac p

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
