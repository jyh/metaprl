(*
 * Define a common tactic type.
 *
 * We build tactics as a layer over the refiner,
 * and the tactics are summarized using Tactic_cache.extract.
 *
 * Eventually, it would be desirable to have tactics just
 * manipulate the Tactic_cache.extract, and perform all
 * search outside the refiner.  Then once the search is
 * complete, the extract would be generated by the refiner.
 *
 * For now, this is too hard.  We use the refiner to guide the
 * search, and we keep the extract up-to-date with the
 * current refinement.  This allows is to use chaining while
 * retaining the traditional search mechanisms.
 *
 * A tactic has two parts:
 *    1. It contains a Refine.tactic
 *)

open Nl_debug
open Printf
open Simple_print

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Refiner.Refiner.Refine

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

(*
 * An extract may be precomputed,
 * or it may be a closure to product the extract.
 * We also make the identity be a special case because it
 * happens so often, and we want to prune it from
 * the resulting extract.
 *)
type extract =
   Extract of Refine.extract * int
 | Compose of extract * extract list
 | Identity

(*
 * Build the thread refiner.
 *)
module ThreadRefinerArg =
struct
   (* Have to do this to avoid type recursion *)
   type extract_aux = extract
   type extract = extract_aux

   let identity = Identity
   let compose ext extl = Compose (ext, extl)
end

module ThreadRefiner = Thread_refiner_tree.MakeThreadRefiner (ThreadRefinerArg)

(*
 * Many tactics wish to examine their argument, so
 * the real type of tactic includes an argument.
 *)
type 'term attribute =
   TermArg of 'term
 | TypeArg of 'term
 | IntArg of int
 | BoolArg of bool
 | SubstArg of 'term
 | TacticArg of tactic
 | IntTacticArg of (int -> tactic)
 | ArgTacticArg of (tactic_arg -> tactic)  (* For tactics that precompile *)
 | TypeinfArg of ((string * 'term) list -> 'term -> (string * 'term) list * 'term)

and 'a attributes = (string * 'a attribute) list

(*
 * Every goal has:
 *   ref_goal: the msequent that is to be proved
 *   ref_label: a label (typically "main") that is used to deescribe the goal
 *   ref_attributes: other attributes that provide info to the tactics
 *   ref_cache: the Tactic_cache.extract that represents this goal
 *   ref_rsrc: the resources that are threaded through the refinement
 *
 *   To increase efficiency, the cache is computed lazily.
 *)
and tactic_arg =
   { ref_goal : msequent;
     ref_label : string;
     ref_attributes : term attributes;
     mutable ref_cache : cache_info;
     ref_sentinal : sentinal
   }

(*
 * The cache is current, or it may be out-of-date.
 *)
and cache_info =
   Current of cache
 | OutOfDate of cache

(*
 * The cache is instantaited with tactic
 * justifications.  This may change at some
 * point.
 *)
and cache        = tactic Tactic_cache.extract

(*
 * A tactic_value is a list of subgoals, and a means for
 * computing the extract.
 *)
and pre_tactic   = prim_tactic
and tactic_value = tactic_arg ThreadRefiner.t
and tactic       = tactic_arg -> tactic_value

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

let remote_server = ThreadRefiner.create print_tactic_arg

(*
 * Create an initial tactic_arg for a proof.
 * Cache is initially out-of-date.  It will be
 * set to the current goal when requested.
 *)
let null_attributes = []

let create sentinal label goal cache attributes =
   { ref_goal = goal;
     ref_label = label;
     ref_attributes = attributes;
     ref_cache = OutOfDate cache;
     ref_sentinal = sentinal
   }

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

let cache arg =
   match arg.ref_cache with
      Current cache ->
         cache
    | OutOfDate cache ->
         let cache = Tactic_cache.set_msequent cache arg.ref_goal in
            arg.ref_cache <- Current cache;
            cache

let label { ref_label = label } =
   label

let attributes { ref_attributes = attributes } =
   attributes

(*
let normalize_attribute (_, arg) =
   match arg with
      TermArg t ->
         normalize_term t
    | TypeArg t ->
         normalize_term t
    | SubstArg t ->
         normalize_term t
    | _ ->
         ()
*)
(*
 * Map a function over the terms in the attributes.
 *)
let rec map_attributes f = function
   [] ->
      []
 | (name, arg) :: tl ->
      let tl = map_attributes f tl in
         match arg with
            TermArg t ->
               (name, TermArg (f t)) :: tl
          | TypeArg t ->
               (name, TypeArg (f t)) :: tl
          | IntArg i ->
               (name, IntArg i) :: tl
          | BoolArg b ->
               (name, BoolArg b) :: tl
          | SubstArg t ->
               (name, SubstArg (f t)) :: tl
          | _ ->
               tl

(*
 * Modify the argument.
 *)
let set_goal arg goal =
   let { ref_goal = seq;
         ref_label = label;
         ref_attributes = attributes;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = arg
   in
      { ref_goal = mk_msequent goal (snd (dest_msequent seq));
        ref_label = label;
        ref_attributes = attributes;
        ref_cache = cache;
        ref_sentinal = sentinal
      }

let set_concl arg concl =
   let { ref_goal = seq;
         ref_label = label;
         ref_attributes = attributes;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = arg
   in
   let goal, hyps = dest_msequent seq in
      { ref_goal = mk_msequent (replace_goal goal concl) hyps;
        ref_label = label;
        ref_attributes = attributes;
        ref_cache = cache;
        ref_sentinal = sentinal
      }

let set_label arg label =
   let { ref_goal = goal;
         ref_attributes = attributes;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = arg
   in
      { ref_goal = goal;
        ref_label = label;
        ref_attributes = attributes;
        ref_cache = cache;
        ref_sentinal = sentinal
      }

(*
 * Attributes.
 *)
let get_term { ref_attributes = attributes } name =
   let rec search = function
      (name', TermArg t) :: tl ->
         if name' = name then
            t
         else
            search tl
    | _ :: tl ->
         search tl
    | [] ->
         raise (RefineError ("get_term", StringStringError ("not found", name)))
   in
      search attributes

let get_type { ref_attributes = attributes } name =
   let rec search = function
      (name', TypeArg t) :: tl ->
         if name' = name then
            t
         else
            search tl
    | _ :: tl ->
         search tl
    | [] ->
         raise (RefineError ("get_type", StringStringError ("not found", name)))
   in
      search attributes

let get_int { ref_attributes = attributes } name =
   let rec search = function
      (name', IntArg t) :: tl ->
         if name' = name then
            t
         else
            search tl
    | _ :: tl ->
         search tl
    | [] ->
         raise (RefineError ("get_int", StringStringError ("not found", name)))
   in
      search attributes

let get_bool { ref_attributes = attributes } name =
   let rec search = function
      (name', BoolArg t) :: tl ->
         if name' = name then
            t
         else
            search tl
    | _ :: tl ->
         search tl
    | [] ->
         raise (RefineError ("get_bool", StringStringError ("not found", name)))
   in
      search attributes

let get_tactic { ref_attributes = attributes } name =
   let rec search = function
      (name', TacticArg t) :: tl ->
         if name' = name then
            t
         else
            search tl
    | _ :: tl ->
         search tl
    | [] ->
         raise (RefineError ("get_tactic", StringStringError ("not found", name)))
   in
      search attributes

let get_int_tactic { ref_attributes = attributes } name =
   let rec search = function
      (name', IntTacticArg t) :: tl ->
         if name' = name then
            t
         else
            search tl
    | (name', _) :: tl ->
         search tl
    | [] ->
         raise (RefineError ("get_int_tactic", StringStringError ("not found", name)))
   in
      search attributes

let get_arg_tactic { ref_attributes = attributes } name =
   let rec search = function
      (name', ArgTacticArg t) :: tl ->
         if name' = name then
            t
         else
            search tl
    | (name', _) :: tl ->
         search tl
    | [] ->
         raise (RefineError ("get_int_tactic", StringStringError ("not found", name)))
   in
      search attributes

let get_typeinf { ref_attributes = attributes } name =
   let rec search = function
      (name', TypeinfArg t) :: tl ->
         if name' = name then
            t
         else
            search tl
    | _ :: tl ->
         search tl
    | [] ->
         raise (RefineError ("get_typeinf", StringStringError ("not found", name)))
   in
      search attributes

let get_subst { ref_attributes = attributes } =
   let rec search = function
      (name, SubstArg t) :: tl ->
         (name, t) :: search tl
    | _ :: tl ->
         search tl
    | [] ->
         []
   in
      search attributes

(*
 * Two args are equal if their goals are equal.
 * Other arguments are ignored.
 *)
let tactic_arg_alpha_equal { ref_goal = goal1 } { ref_goal = goal2 } =
   msequent_alpha_equal goal1 goal2

(************************************************************************
 * REFINEMENT                                                           *
 ************************************************************************)

(*
 * The refiner just applies the tactic to the arg.
 *)
let refine tac arg =
   let x = ThreadRefiner.eval remote_server (tac arg) in
      if !debug_tactic then
         eprintf "Refinement done%t" eflush;
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
      ref_attributes = attributes;
      ref_cache = cache;
      ref_sentinal = sentinal
    } goal =
   let cache =
      match cache with
         Current cache ->
            OutOfDate cache
       | cache ->
            cache
   in
      { ref_goal = goal;
        ref_label = label;
        ref_attributes = attributes;
        ref_cache = cache;
        ref_sentinal = sentinal
      }

(*
 * Construct polymorphic tactic.
 *)
let tactic_of_rule rule (addrs, names) params arg =
   let { ref_goal = goal; ref_sentinal = sentinal } = arg in
   let _ =
      if !debug_tactic then
         eprintf "Collecting addresses%t" eflush
   in
   let rule = rule (addrs, names) params in
   let _ =
      if !debug_tactic then
         eprintf "Starting refinement%t" eflush
   in
   let subgoals, ext = Refine.refine sentinal rule goal in
      if !debug_tactic then
         eprintf "tactic_of_rule done%t" eflush;
      ThreadRefiner.create_value (List.map (make_subgoal arg) subgoals) (Extract (ext, List.length subgoals))

(*
 * Construct polymorphic tactic.
 *)
let tactic_of_refine_tactic rule arg =
   let _ =
      if !debug_tactic then
         eprintf "Starting refinement%t" eflush
   in
   let { ref_goal = goal; ref_sentinal = sentinal } = arg in
   let subgoals, ext = Refine.refine sentinal rule goal in
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
         ref_attributes = attributes;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = arg
   in
      match Refine.refine sentinal rule goal with
         [subgoal], ext ->
            let cache =
               match cache with
                  Current cache ->
                     OutOfDate cache
                | cache ->
                     cache
            in
            let subgoal =
               { ref_goal = subgoal;
                 ref_label = label;
                 ref_attributes = attributes;
                 ref_cache = cache;
                 ref_sentinal = sentinal
               }
            in
               ThreadRefiner.create_value [subgoal] (Extract (ext, 1))
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
         ref_attributes = attributes;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = arg
   in
   let subgoals, ext = Refine.refine sentinal rule goal in
   let cache =
      match cache with
         Current cache ->
            OutOfDate cache
       | cache ->
            cache
   in
   let make_subgoal goal =
      { ref_goal = goal;
        ref_label = label;
        ref_attributes = attributes;
        ref_cache = cache;
        ref_sentinal = sentinal
      }
   in
      ThreadRefiner.create_value (List.map make_subgoal subgoals) (Extract (ext, List.length subgoals))

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
let justify_exn = RefineError ("Tactic_type.justify", StringError "identity tactic failed")

let rec justify extl = function
   Compose (ext, extl') ->
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

 | Identity ->
      match extl with
         ext :: extl ->
            ext, extl
       | [] ->
            raise justify_exn

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
   let i = i - 1 in
      if !debug_refine then
         begin
            let { ref_goal = seq } = p in
            let goal, hyps = dest_msequent seq in
               eprintf "Tactic_type.nthAssumT:\nHyp: %d%t" i eflush;
               List.iter (fun hyp ->
                     SimplePrint.prerr_simple_term hyp;
                     eflush stderr) hyps;
               eprintf "\nGoal: ";
               SimplePrint.prerr_simple_term goal;
               eflush stderr
         end;
      let subgoals, ext = tactic_of_refine_tactic (Refine.nth_hyp i) p in
         ThreadRefiner.create_value subgoals ext

(*
 * Identity doesn't do anything.
 *)
let idT p =
   ThreadRefiner.create_value [p] Identity

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
 * Sequencing tactics.
 *)
let prefix_thenT = ThreadRefiner.compose1
let prefix_thenLT = ThreadRefiner.compose2
let prefix_thenFLT = ThreadRefiner.composef
let firstT = ThreadRefiner.first
let prefix_orelseT tac1 tac2 =
   firstT [tac1; tac2]

(*
 * Modify the label.
 *)
let setLabelT name p =
   let { ref_goal = goal;
         ref_attributes = attributes;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = p
   in
   let p =
      { ref_goal = goal;
        ref_label = name;
        ref_attributes = attributes;
        ref_cache = cache;
        ref_sentinal = sentinal
      }
   in
      ThreadRefiner.create_value [p] Identity

(*
 * Add a term argument.
 *)
let withT attribute tac p =
   let attributes = p.ref_attributes in
   let make_goal
       { ref_goal = goal;
         ref_label = name;
         ref_cache = cache;
         ref_sentinal = sentinal
       } =
      ThreadRefiner.create_value  (**)
         [{ ref_goal = goal;
            ref_label = name;
            ref_attributes = attribute :: attributes;
            ref_cache = cache;
            ref_sentinal = sentinal
          }] Identity
   in
   let make_subgoal p =
      let { ref_goal = goal;
            ref_label = name;
            ref_cache = cache;
            ref_sentinal = sentinal
          } = p
      in
         ThreadRefiner.create_value (**)
            [{ ref_goal = goal;
               ref_label = name;
               ref_attributes = attributes;
               ref_cache = cache;
               ref_sentinal = sentinal
             }]  Identity
   in
      (make_goal thenT tac thenT make_subgoal) p

let withTermT name t =
   withT (name, TermArg t)

let withTypeT name t =
   withT (name, TypeArg t)

let withIntT name i =
   withT (name, IntArg i)

let withBoolT name flag =
   withT (name, BoolArg flag)

let withTacticT name tac =
   withT (name, TacticArg tac)

(*
 * Add some substitutions.
 *)
let withSubstT subst tac arg =
   let { ref_goal = goal;
         ref_label = name;
         ref_attributes = attributes;
         ref_cache = cache;
         ref_sentinal = sentinal
       } = arg
   in
   let rec make_subst = function
      (name, t) :: tl ->
         (name, SubstArg t) :: (make_subst tl)
    | [] ->
         attributes
   in
   let arg =
      { ref_goal = goal;
        ref_label = name;
        ref_attributes = make_subst subst;
        ref_cache = cache;
        ref_sentinal = sentinal
      }
   in
   let make_subgoal arg =
      let { ref_goal = goal;
            ref_label = name;
            ref_cache = cache;

          } = arg
      in
         { ref_goal = goal;
           ref_label = name;
           ref_attributes = attributes;
           ref_cache = cache;
           ref_sentinal = sentinal
         }
   in
   let subgoals, ext = refine tac arg in
      ThreadRefiner.create_value (List.map make_subgoal subgoals) ext

(*
 * Time the tactic.
 *)
let timingT tac arg =
   Utils.time_it tac arg

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
