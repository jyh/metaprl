(*
 * Some basic tacticals.
 *
 * $Log$
 * Revision 1.5  1998/04/13 21:11:18  jyh
 * Added interactive proofs to filter.
 *
 * Revision 1.4  1998/04/09 18:26:13  jyh
 * Working compiler once again.
 *
 * Revision 1.3  1998/02/18 18:48:05  jyh
 * Initial ocaml semantics.
 *
 * Revision 1.2  1997/08/06 16:18:55  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:44  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.1  1996/09/25 22:52:07  jyh
 * Initial "tactical" commit.
 *
 *)

open Term
open Refine_sig
open Refine

open Proof_type

open Sequent
open Tactic_type

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim id : ('t : 'T) --> 'T = 't

let idT = id

(************************************************************************
 * TRIVIAL TACTICS                                                      *
 ************************************************************************)

(* Trivial tactics *)
let failT p =
   raise (RefineError (StringError "Fail"))

let failWithT s p =
   raise (RefineError (StringError s))

(************************************************************************
 * SEQUENCING                                                           *
 ************************************************************************)

(*
 * Sequencing tactics.
 *)
let prefix_orelseT = Refiner.orelse

let prefix_andalsoT = Refiner.andthen

let prefix_thenT = Refiner.andthen

let prefix_thenLT = Refiner.andthenL

let prefix_thenFLT = Refiner.andthenFL

let tryT tac = tac orelseT idT

let prefix_orthenT tac1 tac2 = (tac1 thenT tryT tac2) orelseT tac2

let rec firstT = function
   [tac] ->
      tac
 | tac::tactl ->
      tac orelseT (firstT tactl)
 | [] -> idT

let prefix_then_OnFirstT tac1 tac2 =
   let aux = function
      p::l ->
         let tac2' = tac2 p in
         let rec dup_id = function
            x::t -> (idT x)::(dup_id t)
          | [] -> []
         in
            tac2'::(dup_id l)
    | [] ->
         []
   in
      tac1 thenFLT aux

let prefix_then_OnLastT tac1 tac2 =
   let rec aux = function
      [p] -> [tac2 p]
    | p::t -> (idT p)::(aux t)
    | [] -> []
   in
      tac1 thenFLT aux

let prefix_then_OnSameConclT tac1 tac2 =
   let first p =
      let t = nth_concl (fst p) 0 in
      let second p =
         let t' = nth_concl (fst p) 0 in
            (if alpha_equal t t' then
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
      let t = fst p in
      let aux' p' =
         match p' with
            [(t', _) as p''] ->
               [(if t' = t' then
                    idT
                 else
                    failWithT "progressT") p'']
          | _ ->
               List.map idT p'
      in
         (tac thenFLT aux') p
   in
      aux

(*
 * Repeat, spreading out over subgoals.
 * Stop if there is no progress.
 *)
let repeatT tac =
   let rec aux t p =
      let t' = fst p in
         (if alpha_equal t t' then
             idT
          else
             tac thenT (aux t')) p
   in
   let start p =
      let t = fst p in
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
   [tac] -> tac
 | tac::tactl -> tac thenT (seqT tactl)
 | [] -> idT

(*
 * List is a list version of the then tactic, but only
 * applies to goals with the same conclusion.
 *)
let seqOnSameConclT = function
   [] -> idT
 | tacs ->
      let start p =
         (* Save the first conclusion *)
         let t = nth_concl (fst p) 0 in
         let rec aux tacs p =
            (* Recurse through the tactics *)
            (match tacs with
                tac::tactl ->
                   let t' = nth_concl (fst p) 0 in
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
   ifT (function p -> pred (nth_concl (fst p) 0))

let ifOnHypT pred tac1 tac2 i p =
   (if pred (nth_hyp i p) then
       tac1
    else
       tac2) i p

let ifThenT pred tac1 =
   ifT (function (t, _) -> pred t) tac1 idT

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
 * Get the label from a proof.
 *)
let proof_label (_, { ref_label = label }) = label

(*
 * Add a label attribute.
 *)
let addHiddenLabelT s (t, { ref_args = args; ref_fcache = fcache; ref_rsrc = rsrc }) =
   idT (t, { ref_label = s; ref_args = args; ref_fcache = fcache; ref_rsrc = rsrc })

let removeHiddenLabelT =
   addHiddenLabelT "main"

let keepingLabelT tac p =
   let l = proof_label p in
      (tac thenT addHiddenLabelT l) p

(*
 * Conditional on label.
 *)
let ifLabLT tacs p =
   let lab = proof_label p in
      try
         let tac = List.assoc lab tacs in
            tac p
      with
         Not_found ->
            idT p

let ifLabT lab tac1 tac2 p =
   let lab' = proof_label p in
      (if lab = lab' then
          tac1
       else
          tac2) p

let ifMT tac p =
   (if List.mem (proof_label p) main_labels then
       tac
    else
       idT) p

let ifWT tac p =
   (if (proof_label p) = "wf" then
       tac
    else
       idT) p

let ifET tac p =
   (if proof_label p = "equality" then
       tac
    else
       idT) p
   
let ifAT tac p =
   (if List.mem (proof_label p) main_labels then
       idT
    else
       tac) p

let ifPT tac p =
   (if List.mem (proof_label p) predicate_labels then
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
         if pred (proof_label p) then
            match ts with
               tac::tactl ->
                  (tac p)::(aux tactl ps)
             | [] ->
                  raise (RefineError (StringError "thenMLT: argument mismatch"))
         else
            (idT p)::(aux ts ps)
    | [] ->
         match ts with
            [] -> []
          | _ ->
               raise (RefineError (StringError "thenMLT: argument mismatch"))
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
      let t' = fst p in
         (if alpha_equal t t' then
             idT
          else
             tac thenMT (aux t')) p
   in
   let start p =
      let t = fst p in
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
   [tac] -> tac
 | tac::tactl -> tac thenMT (seqOnMT tactl)
 | [] -> idT
            
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
      let t = fst p in
      let lab = proof_label p in
      let aux' p' =
         match p' with
            [p''] ->
               let t' = fst p'' in
               let lab' = proof_label p'' in
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
   tac (get_pos_hyp_num i p) p

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
    | [] -> idT
   in
      aux clauses

let onHypsT = onClausesT

(*
 * Repeat tactic on main subgoals.
 *)
let onMClausesT clauses tac =
   let rec aux = function
      [i] -> onClauseT i tac
    | i::t -> onClauseT i tac thenMT aux t
    | [] -> idT
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
      aux ((hyp_count p) - 1) p

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
      aux ((hyp_count p) - 1) p
   
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
      aux ((hyp_count p) - 1) p

(*
 * Variable name addressing.
 *)
let onVarT v tac p =
   let i =
      try get_decl_number p v with
         Not_found ->
            raise (RefineError (StringError ("onVarT: var not found: " ^ v)))
   in
      tac i p

(************************************************************************
 * ARGUMENTS                                                            *
 ************************************************************************)

(*
 * Push args.
 *)
let withArgListT args tac (goal, { ref_label = label;
                                   ref_args = args';
                                   ref_fcache = fcache;
                                   ref_rsrc = rsrc
                           }) =
   let restoreArgListT (goal', { ref_label = label'; ref_fcache = fcache; ref_rsrc = rsrc }) =
      idT (goal', { ref_label = label'; ref_args = args'; ref_fcache = fcache; ref_rsrc = rsrc })
   in
      (tac thenT restoreArgListT) (goal, { ref_label = label;
                                           ref_args = args @ args';
                                           ref_fcache = fcache;
                                           ref_rsrc = rsrc
                                   })

let withArgT arg tac (goal, { ref_label = label;
                              ref_args = args';
                              ref_fcache = fcache;
                              ref_rsrc = rsrc
                      }) =
   let restoreArgListT (goal', { ref_label = label'; ref_fcache = fcache; ref_rsrc = rsrc }) =
      idT (goal', { ref_label = label'; ref_args = args'; ref_fcache = fcache; ref_rsrc = rsrc })
   in
      (tac thenT restoreArgListT) (goal, { ref_label = label;
                                           ref_args = arg::args';
                                           ref_fcache = fcache;
                                           ref_rsrc = rsrc
                                   })

(*
 * Get an arg, given a test.
 *)
let get_arg test (_, { ref_args = args }) =
   let rec aux = function
      h::t ->
         begin
            match test h with
               Some x -> x
             | None -> aux t
         end
    | [] -> raise Not_found
   in
      aux args

(*
 * A particular argument.
 *)
let withT t = withArgT (TermArgs [t])

let get_term_arg i =
   let test = function
      TermArgs l -> Some (List.nth l i)
    | _ -> None
   in
      get_arg test

let get_term_args =
   let test = function
      TermArgs l -> Some l
    | _ -> None
   in
      get_arg test

(*
 * For renaming variables.
 *)
let newT vars = withArgT (VarArgs vars)

let get_var_arg i =
   let test = function
      VarArgs l -> Some (List.nth l i)
    | _ -> None
   in
      get_arg test

let get_var_args =
   let test = function
      VarArgs l -> Some l
    | _ -> None
   in
      get_arg test

(*
 * Substitutions.
 *)
let usingT subst =
   withArgT (SubstArg subst)

let get_subst_arg =
   let test = function
      SubstArg s -> Some s
    | _ -> None
   in
      get_arg test

(*
 * Type arg.
 *)
let atT t =
   withArgT (TypeArg t)

let get_type_arg =
   let test = function
      TypeArg t -> Some t
    | _ -> None
   in
      get_arg test

(*
 * Int arg.
 *)
let selT i =
   withArgT (IntArgs [i])

let get_int_arg i =
   let test = function
      IntArgs l -> Some (List.nth l i)
    | _ -> None
   in
      get_arg test

let get_int_args =
   let test = function
      IntArgs l -> Some l
    | _ -> None
   in
      get_arg test

(*
 * Thinning behavior of tactics.
 *)
let notThinningT =
   withArgT (ThinArg false)

let thinningT =
   withArgT (ThinArg true)

let get_thinning_arg =
   let test = function
      ThinArg p -> Some p
    | _ -> None
   in
      get_arg test

(*
 * -*-
 * Local Variables:
 * Caml-master: "/usr/local/lib/nuprl-light/camlp4o.run"
 * End:
 * -*-
 *)
