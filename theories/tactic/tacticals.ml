(*
 * Some basic tacticals.
 *
 *)

include Nltop

open Printf
open Nl_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError

open Sequent

(*
 * Debug statement.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Tacticals%t" eflush

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

type tactic = Tactic_type.tactic
type cache = Tactic_type.cache

(************************************************************************
 * TRIVIAL TACTICS                                                      *
 ************************************************************************)

(* Basic refinement *)
let refine = Tactic_type.refine
let compose = Tactic_type.compose
let term_of_extract = Tactic_type.term_of_extract

(* Trivial tactics *)
let idT =
   Tactic_type.idT

let failT p =
   raise (RefineError ("failT", StringError "Fail"))

let failWithT s p =
   raise (RefineError ("failWithT", StringError s))

let timingT =
   Tactic_type.timingT

let nthAssumT =
   Tactic_type.nthAssumT

(************************************************************************
 * SEQUENCING                                                           *
 ************************************************************************)

let prefix_orelseT = Tactic_type.prefix_orelseT
let prefix_andalsoT = Tactic_type.prefix_thenT
let prefix_thenT = Tactic_type.prefix_thenT
let prefix_thenLT = Tactic_type.prefix_thenLT
let prefix_thenFLT = Tactic_type.prefix_thenFLT

let tryT tac =
   tac orelseT idT

let prefix_orthenT tac1 tac2 =
   (tac1 thenT tryT tac2) orelseT tac2

let rec firstT = function
   [tac] ->
      tac
 | tac :: tactl ->
      tac orelseT (firstT tactl)
 | [] ->
      (fun p -> raise (RefineError ("firstT", StringError "no tactics")))

let prefix_then_OnFirstT tac1 tac2 =
   let aux = function
      p::l ->
         let tac2' = tac2 p in
         let rec dup_id = function
            x::t ->
               idT x :: dup_id t
          | [] ->
               []
         in
            tac2' :: dup_id l
    | [] ->
         []
   in
      tac1 thenFLT aux

let prefix_then_OnLastT tac1 tac2 =
   let rec aux = function
      [p] ->
         [tac2 p]
    | p::t ->
         idT p :: aux t
    | [] ->
         []
   in
      tac1 thenFLT aux

let prefix_then_OnSameConclT tac1 tac2 =
   let first p =
      let t = Sequent.concl p in
      let second p =
         (if alpha_equal t (Sequent.concl p) then
             tac2
          else
             idT) p
      in
         (tac1 thenT second) p
   in
      first

(************************************************************************
 * PROGRESS                                                             *
 ************************************************************************)

(* Allow tactic only if no subgoals *)
let completeT tac =
   tac thenT (failWithT "completeT")

(*
 * Apply the tactic and fail if there is only
 * one subgoal and it is the same.
 *)
let progressT tac =
   let aux p =
      let t = Sequent.goal p in
      let tac' p =
         match p with
            [p] ->
               if alpha_equal (Sequent.goal p) t then
                  raise (RefineError ("progressT", StringError "no progress"))
               else
                  [idT p]
          | _ ->
               List.map idT p
      in
         (tac thenFLT tac') p
   in
      aux

(*
 * Repeat, spreading out over subgoals.
 * Stop if there is no progress.
 *)
let repeatT tac =
   let rec aux t p =
      let t' = Sequent.goal p in
         (if alpha_equal t t' then
             idT
          else
             tac thenT (aux t')) p
   in
   let start p =
      let t = Sequent.goal p in
         (tac thenT (aux t)) p
   in
      start

(*
 * Repeat a tactic for a fixed number of times.
 *)
let repeatForT i tac =
   if i = 0 then
      idT
   else
      let rec aux i =
         if i = 1 then
            tac
         else
            tac thenT (aux (i - 1))
      in
         aux i

(*
 * Seuqence the tacs.
 *)
let rec seqT = function
   [tac] ->
      tac
 | tac::tactl ->
      tac thenT (seqT tactl)
 | [] ->
      idT

(*
 * List is a list version of the then tactic, but only
 * applies to goals with the same conclusion.
 *)
let seqOnSameConclT = function
   [] ->
      idT
 | tacs ->
      let start p =
         (* Save the first conclusion *)
         let t = Sequent.concl p in
         let rec aux tacs p =
            (* Recurse through the tactics *)
            (match tacs with
                tac::tactl ->
                   let t' = Sequent.concl p in
                      if alpha_equal t t' then
                         tac thenT (aux tactl)
                      else
                         idT
              | [] -> idT) p
         in
            aux tacs p
      in
         start

(************************************************************************
 * CONDITIONALS                                                         *
 ************************************************************************)

(*
 * Conditionals.
 *)
let ifT pred tac1 tac2 p =
   (if pred p then
       tac1
    else
       tac2) p

let ifOnConclT pred =
   ifT (function p -> pred (Sequent.concl p))

let ifOnHypT pred tac1 tac2 i p =
   (if pred (snd (Sequent.nth_hyp p i)) then
       tac1
    else
       tac2) i p

let ifThenT pred tac1 =
   ifT (function p -> pred (Sequent.goal p)) tac1 idT

let ifThenOnConclT pred tac =
   let failT = failWithT "ifThenOnConclT" in
      ifOnConclT pred tac failT

let ifThenOnHypT pred tac i =
   let failT _ = failWithT "ifThenOnHypT" in
      ifOnHypT pred tac failT i

let whileT pred tac =
   let rec aux p =
      tryT (ifThenT pred (progressT tac thenT aux)) p
   in
      aux

let untilT pred =
   whileT (function p -> not (pred p))

(************************************************************************
 * LABEL TACTICS                                                        *
 ************************************************************************)

(*
 * Label tactics.
 *)
let main_labels =
   ["main";
    "upcase";
    "downcase";
    "basecase";
    "truecase";
    "falsecase";
    "subterm"]

let predicate_labels =
   ["set predicate";
    "rewrite subgoal";
    "assertion";
    "antecedent"]

(*
 * Add a label attribute.
 *)
let addHiddenLabelT = Tactic_type.setLabelT

let removeHiddenLabelT =
   addHiddenLabelT "main"

let keepingLabelT tac p =
   let label = Sequent.label p in
      (tac thenT addHiddenLabelT label) p

(*
 * Conditional on label.
 *)
let ifLabLT tacs p =
   let lab = Sequent.label p in
      try
         let tac = List.assoc lab tacs in
            tac p
      with
         Not_found ->
            idT p

let ifLabT lab tac1 tac2 p =
   let lab' = Sequent.label p in
      (if lab = lab' then
          tac1
       else
          tac2) p

let ifMT tac p =
   (if List.mem (Sequent.label p) main_labels then
       tac
    else
       idT) p

let ifWT tac p =
   (if (Sequent.label p) = "wf" then
       tac
    else
       idT) p

let ifET tac p =
   (if Sequent.label p = "equality" then
       tac
    else
       idT) p

let ifAT tac p =
   (if List.mem (Sequent.label p) main_labels then
       idT
    else
       tac) p

let ifPT tac p =
   (if List.mem (Sequent.label p) predicate_labels then
       tac
    else
       idT) p

(*
 * Label tacticals.
 *)
let prefix_thenLabLT tac1 tacs =
   tac1 thenT ifLabLT tacs

let prefix_thenMT tac1 tac2 =
   tac1 thenT ifMT tac2

let prefix_thenAT tac1 tac2 =
   tac1 thenT ifAT tac2

let prefix_thenWT tac1 tac2 =
   tac1 thenT ifWT tac2

let prefix_thenET tac1 tac2 =
   tac1 thenT ifET tac2

let prefix_thenPT tac1 tac2 =
   tac1 thenT ifPT tac2

(*
 * Apply the tactic list only to the specified subgoals.
 *)
let thenLLT pred tac1 tacs =
   let rec aux ts = function
      p::ps ->
         if pred (Sequent.label p) then
            match ts with
               tac::tactl ->
                  (tac p)::(aux tactl ps)
             | [] ->
                  raise (RefineError ("thenMLT", StringError "argument mismatch"))
         else
            (idT p)::(aux ts ps)
    | [] ->
         match ts with
            [] -> []
          | _ ->
               raise (RefineError ("thenMLT", StringError "argument mismatch"))
   in
      tac1 thenFLT (aux tacs)

let prefix_thenMLT =
   thenLLT (function l -> List.mem l main_labels)

let prefix_thenALT =
   thenLLT (function l -> not (List.mem l main_labels))

(************************************************************************
 * LABEL PROGRESS                                                       *
 ************************************************************************)

(*
 * Repeat only on main subgoals.
 *)
let repeatMT tac =
   let rec aux t p =
      let t' = Sequent.goal p in
         (if alpha_equal t t' then
             idT
          else
             tac thenMT (aux t')) p
   in
   let start p =
      let t = Sequent.goal p in
         (tac thenMT (aux t)) p
   in
      start

(*
 * Repeat a fixed number of times on main subgoals.
 *)
let repeatMForT i tac =
   if i = 0 then
      idT
   else
      let rec aux i =
         if i = 1 then
            tac
         else
            tac thenMT (aux (i - 1))
      in
         aux i

(*
 * Sequence tactics on main subgoals.
 *)
let rec seqOnMT = function
   [tac] ->
      tac
 | tac::tactl ->
      tac thenMT (seqOnMT tactl)
 | [] ->
      idT

(*
 * Make sure no main subgoals.
 *)
let completeMT tac =
   tac thenMT failWithT "completeMT"

(*
 * Note changes of label, as well as changes in sequent.
 *)
let labProgressT tac =
   let aux p =
      let t = Sequent.goal p in
      let lab = Sequent.label p in
      let aux' p' =
         match p' with
            [p''] ->
               let t' = Sequent.goal p'' in
               let lab' = Sequent.label p'' in
                  [(if alpha_equal t t' & lab = lab' then
                       idT
                    else
                       failWithT "progressT") p'']
          | _ ->
               List.map idT p'
      in
         (tac thenFLT aux') p
   in
      aux

(************************************************************************
 * HYP AND CLAUSE                                                       *
 ************************************************************************)

(*
 * Renumbering.
 *)
let onClauseT i tac p =
   tac i p

let onHypT = onClauseT

let onConclT tac = tac 0

(*
 * Repeat tactic on all subgoals.
 *)
let onClausesT clauses tac =
   let rec aux = function
      [i] ->
         onClauseT i tac
    | i::t ->
         onClauseT i tac thenT aux t
    | [] ->
         idT
   in
      aux clauses

let onHypsT = onClausesT

(*
 * Repeat tactic on main subgoals.
 *)
let onMClausesT clauses tac =
   let rec aux = function
      [i] ->
         onClauseT i tac
    | i::t ->
         onClauseT i tac thenMT aux t
    | [] ->
         idT
   in
      aux clauses

let onMHypsT = onMClausesT

(*
 * Work on all hyps.
 *)
let onAllHypsT tac p =
   let rec aux i =
      if i = 1 then
         tac i
      else if i > 1 then
         tac i thenT (aux (i - 1))
      else
         idT
   in
      aux (Sequent.hyp_count p) p

(*
 * Include conclusion.
 *)
let onAllClausesT tac =
   onAllHypsT tac thenT onConclT tac

(*
 * Try forms.
 *)
let tryOnAllHypsT tac =
   onAllHypsT (function i -> tryT (tac i))

let tryOnAllClausesT tac =
   onAllClausesT (function i -> tryT (tac i))

(*
 * Labelled forms.
 *)
let onAllMHypsT tac p =
   let rec aux i =
      if i = 1 then
         tac i
      else if i > 1 then
         tac i thenMT (aux (i - 1))
      else
         idT
   in
      aux (Sequent.hyp_count p) p

let onAllMClausesT tac =
   onAllMHypsT tac thenMT onConclT tac

let tryOnAllMHypsT tac =
   onAllMHypsT (function i -> tryT (tac i))

let tryOnAllMClausesT tac =
   onAllMClausesT (function i -> tryT (tac i))

(*
 * Make sure one of the hyps works.
 *)
let onSomeHypT tac p =
   let rec aux i =
      if i = 1 then
         tac i
      else if i > 1 then
         tac i orelseT (aux (i - 1))
      else
         idT
   in
      aux (Sequent.hyp_count p) p

(*
 * Variable name addressing.
 *)
let onVarT v tac p =
   let i =
      try Sequent.get_decl_number p v with
         Not_found ->
            raise (RefineError ("onVarT", StringStringError (v, "variable not found")))
   in
      tac i p

(************************************************************************
 * ARGUMENTS                                                            *
 ************************************************************************)


let withTermT   = Tactic_type.withTermT
let withTypeT   = Tactic_type.withTypeT
let withBoolT   = Tactic_type.withBoolT
let withIntT    = Tactic_type.withIntT
let withSubstT  = Tactic_type.withSubstT
let withTacticT = Tactic_type.withTacticT

let withT     = withTermT "with"
let usingT    = withSubstT
let atT       = withTypeT "univ"
let selT      = withIntT  "sel"
let thinningT = withBoolT "thin"

let get_with_arg arg =
   get_term_arg arg "with"

let get_univ_arg arg =
   get_type_arg arg "univ"

let get_sel_arg arg =
   get_int_arg arg "sel"

let get_thinning_arg arg =
   try get_bool_arg arg "thin" with
      RefineError _ ->
         true

(*
 * -*-
 * Local Variables:
 * Caml-master: "/usr/local/lib/nuprl-light/camlp4o.run"
 * End:
 * -*-
 *)
