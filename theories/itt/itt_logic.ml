(*
 * Regular logic connectives.
 *
 *)

include Itt_equal
include Itt_dprod
include Itt_union
include Itt_void
include Itt_unit
include Itt_soft
include Itt_struct

open Printf
open Debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Conversionals
open Sequent

open Base_auto_tactic
open Base_dtactic

open Itt_squash
open Itt_void
open Itt_equal
open Itt_soft
open Itt_rfun
open Itt_dprod
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_logic%t" eflush

let debug_auto =
   create_debug (**)
      { debug_name = "auto";
        debug_description = "Display auto tactic operations";
        debug_value = false
      }

(************************************************************************
 * REWRITES								*
 ************************************************************************)

declare "prop"[@i:l]

declare "true"
declare "false"
declare "not"{'a}
declare "iff"{'a; 'b}
declare "implies"{'a; 'b}
declare "and"{'a; 'b}
declare "or"{'a; 'b}
declare "all"{'A; x. 'B['x]}
declare "exists"{'A; x. 'B['x]}

primrw unfoldProp : "prop"[@i:l] <--> "univ"[@i:l]

primrw unfoldTrue : "true" <--> unit
primrw unfoldFalse : "false" <--> void
primrw unfoldNot : not{'a} <--> 'a -> void
primrw unfoldImplies : 'a => 'b <--> 'a -> 'b
primrw unfoldIff : "iff"{'a; 'b} <--> (('a -> 'b) & ('b -> 'a))
primrw unfoldAnd : 'a & 'b <--> 'a * 'b
primrw unfoldOr : 'a or 'b <--> 'a + 'b
primrw unfoldAll : all x: 'A. 'B['x] <--> x:'A -> 'B['x]
primrw unfoldExists : exst x: 'A. 'B['x] <--> x:'A * 'B['x]

primrw reducePropTrue : "prop"["true":t] <--> "true"
primrw reducePropFalse : "prop"["false":t] <--> "false"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * All elimination performs a thinning
 *)
interactive allElimination 'H 'J 'w 'z :
   sequent [squash] { 'H; x: all a: 'A. 'B['a]; 'J['x] >- 'z = 'z in 'A } -->
   sequent ['ext] { 'H; x: all a: 'A. 'B['a]; 'J['x]; w: 'B['z] >- 'C['x] } -->
   sequent ['ext] { 'H; x: all a: 'A. 'B['a]; 'J['x] >- 'C['x] }

(*
 * IFF typehood.
 *)
interactive iffType 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{iff{'A; 'B}} }

(************************************************************************
 * DISPLAY FORMS							*
 ************************************************************************)

prec prec_iff
prec prec_implies
prec prec_and
prec prec_or
prec prec_quant

prec prec_implies < prec_iff
prec prec_iff < prec_or
prec prec_or < prec_and
prec prec_quant < prec_iff

dform true_df1 : mode[src] :: "true" = `"True"

dform false_df1 : mode[src] :: "false" = `"False"

dform not_df1 : mode[src] :: parens :: "prec"[prec_implies] :: "not"{'a} =
   `"not " slot[le]{'a}

dform implies_df1 : mode[src] :: parens :: "prec"[prec_implies] :: implies{'a; 'b} =
   slot[le]{'a} `" => " slot[lt]{'b}

dform iff_df1 : mode[src] :: parens :: "prec"[prec_iff] :: iff{'a; 'b} =
   slot[le]{'a} `" <==> " slot[lt]{'b}

dform and_df1 : mode[src] :: parens :: "prec"[prec_and] :: "and"{'a; 'b} =
   slot[le]{'a} `" /\\ " slot[lt]{'b}

dform or_df1 : mode[src] :: parens :: "prec"[prec_or] :: "or"{'a; 'b} =
   slot[le]{'a} `" \\/ " slot[lt]{'b}

dform all_df1 : mode[src] :: parens :: "prec"[prec_quant] :: "all"{'A; x. 'B} =
   `"all " slot{'x} `": " slot{'A}`"." slot{'B}

dform exists_df1 : mode[src] :: parens :: "prec"[prec_quant] :: "exists"{'A; x. 'B} =
  `"exists " slot{'x} `": " slot{'A} `"." slot{'B}

dform true_df2 : mode[prl] :: "true" =
   `"True"

dform false_df2 : mode[prl] :: "false" =
   `"False"

dform not_df2 : mode[prl] :: parens :: "prec"[prec_implies] :: "not"{'a} =
   Nuprl_font!tneg slot[le]{'a}

dform implies_df2 : mode[prl] :: parens :: "prec"[prec_implies] :: implies{'a; 'b} =
   slot[le]{'a} " " Nuprl_font!Rightarrow " " slot[lt]{'b}

dform iff_df2 : mode[prl] :: parens :: "prec"[prec_iff] :: iff{'a; 'b} =
   slot[le]{'a} " " Nuprl_font!Leftrightarrow " " slot[lt]{'b}

dform and_df1 : mode[prl] :: parens :: "prec"[prec_and] :: "and"{'a; 'b} =
   slot[le]{'a} " " Nuprl_font!wedge " " slot[lt]{'b}

dform or_df2 : mode[prl] :: parens :: "prec"[prec_or] :: "or"{'a; 'b} =
   slot[le]{'a} " " Nuprl_font!vee " " slot[lt]{'b}

dform all_df2 : mode[prl] :: parens :: "prec"[prec_quant] :: "all"{'A; x. 'B} =
   pushm[3] Nuprl_font!forall slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm

dform exists_df2 : mode[prl] :: parens :: "prec"[prec_quant] :: "exists"{'A; x. 'B} =
   pushm[3] Nuprl_font!"exists" slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let true_term = << "true" >>
let is_true_term t = t = true_term

let false_term = << "false" >>
let is_false_term t = t = false_term

let all_term = << all x: 'A. 'B['x] >>
let all_opname = opname_of_term all_term
let is_all_term = is_dep0_dep1_term all_opname
let dest_all = dest_dep0_dep1_term all_opname
let mk_all_term = mk_dep0_dep1_term all_opname

let exists_term = << exst x: 'A. 'B['x] >>
let exists_opname = opname_of_term exists_term
let is_exists_term = is_dep0_dep1_term exists_opname
let dest_exists = dest_dep0_dep1_term exists_opname
let mk_exists_term = mk_dep0_dep1_term exists_opname

let or_term = << 'A or 'B >>
let or_opname = opname_of_term or_term
let is_or_term = is_dep0_dep0_term or_opname
let dest_or = dest_dep0_dep0_term or_opname
let mk_or_term = mk_dep0_dep0_term or_opname

let and_term = << 'A and 'B >>
let and_opname = opname_of_term and_term
let is_and_term = is_dep0_dep0_term and_opname
let dest_and = dest_dep0_dep0_term and_opname
let mk_and_term = mk_dep0_dep0_term and_opname

let implies_term = << 'A => 'B >>
let implies_opname = opname_of_term implies_term
let is_implies_term = is_dep0_dep0_term implies_opname
let dest_implies = dest_dep0_dep0_term implies_opname
let mk_implies_term = mk_dep0_dep0_term implies_opname

let iff_term = << "iff"{'A; 'B} >>
let iff_opname = opname_of_term iff_term
let is_iff_term = is_dep0_dep0_term iff_opname
let dest_iff = dest_dep0_dep0_term iff_opname
let mk_iff_term = mk_dep0_dep0_term iff_opname

let not_term = << "not"{'a} >>
let not_opname = opname_of_term not_term
let is_not_term = is_dep0_term not_opname
let dest_not = dest_dep0_term not_opname
let mk_not_term = mk_dep0_term not_opname

(*
 * D
 *)
let terms =
   [true_term,    unfoldTrue;
    false_term,   unfoldFalse;
    all_term,     unfoldAll;
    exists_term,  unfoldExists;
    or_term,      unfoldOr;
    and_term,     unfoldAnd;
    implies_term, unfoldImplies;
    iff_term,     unfoldIff;
    not_term,     unfoldNot]

let add arg =
   let rec aux (dr, er) = function
      (t, rw)::tl ->
         aux (add_soft_abs dr er t rw) tl
    | [] ->
         (dr, er)
   in
      aux arg

let d_resource, eqcd_resource = add (d_resource, eqcd_resource) terms

(*
 * Special elimination case for all.
 *)
let d_allT i p =
   if i = 0 then
      (rw unfoldAll 0 thenT dT 0) p
   else
      let w = get_with_arg p in
      let j, k = hyp_indices p i in
      let v = Var.maybe_new_vars1 p "v" in
         (allElimination j k v w
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p

let all_term = << all a: 'A. 'B['a] >>

let d_resource = d_resource.resource_improve d_resource (all_term, d_allT)

(*
 * Special case for iff.
 *)
let d_iff_typeT i p =
   if i = 0 then
      iffType (Sequent.hyp_count p) p
   else
      raise (RefineError ("d_iff_typeT", StringError "no elimination form"))

let iff_type_term = << "type"{iff{'A; 'B}} >>

let d_resource = d_resource.resource_improve d_resource (iff_type_term, d_iff_typeT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of true, false.
 *)
let inf_univ1 _ decl _ = decl, univ1_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (true_term, inf_univ1)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (false_term, inf_univ1)

(*
 * Type of quantifiers.
 *)
let inf_d dest f decl t =
   let v, a, b = dest t in
   let decl', a' = f decl a in
   let decl'', b' = f ((v, a)::decl') b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (all_term, inf_d dest_all)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (exists_term, inf_d dest_exists)

(*
 * Type of propositions.
 *)
let inf_nd dest f decl t =
   let a, b = dest t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (or_term, inf_nd dest_or)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (and_term, inf_nd dest_and)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (implies_term, inf_nd dest_implies)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (iff_term, inf_nd dest_iff)

(*
 * Type of all.
 *)
let inf_not f decl t =
   let a = dest_not t in
      f decl a

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (not_term, inf_not)

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

(*
 * Decompose universal formulas.
 *)
let rec univCDT p =
   let concl = Sequent.concl p in
      if is_all_term concl
         or is_dfun_term concl
         or is_implies_term concl
         or is_fun_term concl
      then
         (dT 0 thenMT univCDT) p
      else
         idT p

let rec genUnivCDT p =
   let concl = Sequent.concl p in
      if is_all_term concl
         or is_dfun_term concl
         or is_implies_term concl
         or is_fun_term concl
         or is_and_term concl
         or is_prod_term concl
         or is_iff_term concl
      then
         (dT 0 thenMT genUnivCDT) p
      else
         idT p

(*
 * Instantiate a hyp with some arguments.
 *)
let instHypT args i =
   let rec inst i firstp args p =
      match args with
         [] ->
            idT p
       | arg :: args' ->
            let _, hyp = nth_hyp p i in
            let tailT args =
               if firstp then
                  inst ((hyp_count p) + 1) false args
               else
                  thinT i thenT inst i false args
            in
               if is_all_term hyp or is_dfun_term hyp then
                  (withT arg (dT i) thenMT tailT args') p
               else if is_implies_term hyp or is_fun_term hyp then
                  (dT i thenMT tailT args) p
               else
                  raise (RefineError ("instHypT", StringTermError ("hyp is not quantified", hyp)))
   in
      inst i true args

(*
 * This type is used to collect the arguments to instantiate.
 *)
type formula_args =
   AllTerm of string * term
 | ImpliesTerm
 | IffLeft
 | IffRight

(*
 * Print an info list.
 *)
let eprint_info info =
   let print_item = function
      AllTerm (v, t) ->
         eprintf "\tAllTerm %s: %a\n" v Simple_print.print_simple_term_fp t
    | ImpliesTerm ->
         eprintf "\tImpliesTerm\n"
    | IffLeft ->
         eprintf "\tIffLeft\n"
    | IffRight ->
         eprintf "\tIffRight\n"
   in
      List.iter print_item info;
      eprintf "\t.%t" eflush

(*
 * Lookup and remove a value from an association list.
 *)
let rec assoc v = function
   (v', t) :: tl ->
      if v' = v then
         t, tl
      else
         let t', tl = assoc v tl in
            t', (v', t) :: tl
 | [] ->
      raise Not_found

(*
 * Check for exact matches.
 *)
let check_subst subst =
   let check (v, t) =
      if !debug_auto then
         eprintf "check_subst: checking %s/%a%t" v Simple_print.print_simple_term_fp t eflush;
      if not (is_var_term t & dest_var t = v) then
         raise (RefineError ("check_subst", StringError "bad match"))
   in
      List.iter check subst

(*
 * Instantiate the vars with the values in the substitution.
 * If any vars in the subst don't match, they are global,
 * and they should match exactly.
 *)
let instantiate_vars args subst =
   if !debug_auto then
      begin
         let print_subst (v, t) =
            eprintf "\t%s: %a%t" v Simple_print.print_simple_term_fp t eflush
         in
            eprintf "instantiate_vars: got subst\n";
            List.iter print_subst subst
      end;
   let rec collect result args subst =
      match args with
         [] ->
            check_subst subst;
            result
       | hd::tl ->
            match hd with
               AllTerm (v, t) ->
                  if !debug_auto then
                     eprintf "instantiate_vars: looking for %s%t" v eflush;
                  let t', subst' = assoc v subst in
                     collect (AllTerm (v, t') :: result) tl subst'
             | ImpliesTerm
             | IffLeft
             | IffRight ->
                  collect (hd :: result) tl subst
   in
      collect [] args subst

(*
 * Walk down an implication and look for the goal.
 *)
let rec match_goal args form goal =
   try
      if !debug_auto then
         eprintf "Matching form%t" eflush;
      let subst = match_terms [] form goal in
      let info = instantiate_vars args subst in
         if !debug_auto then
            eprintf "Form matched%t" eflush;
         info
   with
      RefineError _ ->
         if is_all_term form then
            let v, v_T, v_P = dest_all form in
               match_goal (AllTerm (v, v_T) :: args) v_P goal
         else if is_dfun_term form then
            let v, v_T, v_P = dest_dfun form in
               match_goal (AllTerm (v, v_T) :: args) v_P goal
         else if is_implies_term form then
            let v_T, v_P = dest_implies form in
               match_goal (ImpliesTerm :: args) v_P goal
         else if is_fun_term form then
            let v_T, v_P = dest_fun form in
               match_goal (ImpliesTerm :: args) v_P goal
         else if is_iff_term form then
            let left, right = dest_iff form in
               try match_goal (IffLeft :: args) left goal with
                  RefineError _ ->
                     match_goal (IffRight :: args) right goal
         else
            raise (RefineError ("match_goal", StringError "no match"))
    | Not_found ->
         raise (RefineError ("match_goal", StringError "no match"))

(*
 * Try the universal #1.
 *)
let backThruHypT i p =
   if !debug_auto then
      eprintf "Starting backThruHyp %d%t" i eflush;
   let rec tac info i firstp p =
      (match info with
          [] ->
             nthHypT i
        | hd :: args ->
             if !debug_auto then
                eprintf "\tbackThruHyp step%t" eflush;
             let tailT =
                if firstp then
                   [idT; tac args ((hyp_count p) + 1) false]
                else
                   [thinT i; thinT i thenT tac args i false]
             in
                match hd with
                   ImpliesTerm ->
                      dT i thenLT tailT
                 | IffRight ->
                      dT i thenT thinT (i + 1) thenT dT i thenLT tailT
                 | IffLeft ->
                      dT i thenT thinT i thenT dT i thenLT tailT
                 | AllTerm (v, t) ->
                      withT t (dT i) thenLT tailT) p
   in
   let _, hyp = nth_hyp p i in
   let goal = Sequent.concl p in
   let info = match_goal [] hyp goal in
      if !debug_auto then
         begin
            eprintf "backThruHyp %d%t" i eflush;
            eprint_info info
         end;
      tac info i true p

(*
 * We can also backchain through assumptions by pulling them
 * in as universally quantified formulas.
 * We assum that we can thin enough.
 *
 * This next function adds the assumption as a universlly
 * quantified formula.
 *)
let assumT i p =
   let goal, assums = dest_msequent (Sequent.msequent p) in
   let assum = List.nth assums (i - 1) in
   let len = TermMan.num_hyps assum in

   (*
    * Compute the number of matching hyps.
    * This is approximate.  Right now, we look
    * for the last context hyp.
    *)
   let rec last_match last_con hyp_index = function
      [] ->
         last_con
    | h::t ->
         match h with
            Hypothesis _ ->
               last_match last_con (hyp_index + 1) t
          | Context _ ->
               last_match hyp_index (hyp_index + 1) t
   in
   let { sequent_hyps = hyps } = TermMan.explode_sequent assum in
   let index = last_match 1 1 hyps in

   (* Construct the assumption as a universal formula *)
   let rec collect j =
      if j = len then
         TermMan.nth_concl assum 0
      else
         let v, hyp = TermMan.nth_hyp assum j in
            mk_all_term v hyp (collect (j + 1))
   in
   let form = collect index in
   let _ =
      if !debug_auto then
         eprintf "Found assumption: %a%t" Simple_print.print_simple_term_fp form eflush
   in

   (* Call intro form on each arg *)
   let rec introT j p =
      if j = len then
         let goal, assums = dest_msequent (Sequent.msequent p) in
         let assum = List.nth assums (i - 1) in
            if is_squash_sequent goal then
               if is_squash_sequent assum then
                  nthAssumT i p
               else
                  (unsquashT (get_squash_arg assum) thenT nthAssumT i) p
            else
               nthAssumT i p
      else
         (dT 0 thenMT introT (j + 1)) p
   in
      (assertT form
       thenLT [thinAllT (index + 1) (TermMan.num_hyps goal) thenT introT index;
               addHiddenLabelT "main"]) p

(*
 * Now try backchaining through the assumption.
 *)
let backThruAssumT i p =
   let j = hyp_count p + 1 in
      (assumT i thenMT (backThruHypT j thenT thinT j)) p

(************************************************************************
 * AUTO TACTIC                                                          *
 ************************************************************************)

(*
 * In auto tactic, Ok to decompose product hyps.
 *)
let logic_trivT i p =
   let _, hyp = nth_hyp p i in
      if is_void_term hyp or is_false_term hyp then
         dT i p
      else
         raise (RefineError ("logic_trivT", StringTermError ("nothing known about", hyp)))

let trivial_resource =
   trivial_resource.resource_improve trivial_resource (**)
      { auto_name = "logic_trivT";
        auto_prec = trivial_prec;
        auto_tac = onSomeHypT logic_trivT
      }

(*
 * Backchaining in auto tactic.
 *)
let logic_autoT i p =
   let _, hyp = nth_hyp p i in
      if is_and_term hyp
         or is_prod_term hyp
         or is_dprod_term hyp
         or is_exists_term hyp
      then
         dT i p
      else
         raise (RefineError ("logic_autoT", StringError "unknown formula"))

let logic_prec = create_auto_prec [trivial_prec] []
let back_hyp_prec = create_auto_prec [logic_prec] []
let back_assum_prec = create_auto_prec [back_hyp_prec] []

let auto_resource =
   auto_resource.resource_improve auto_resource (**)
      { auto_name = "logic_autoT";
        auto_prec = logic_prec;
        auto_tac = auto_wrap (onSomeHypT logic_autoT)
      }

let auto_resource =
   auto_resource.resource_improve auto_resource (**)
      { auto_name = "backThruHypT";
        auto_prec = back_hyp_prec;
        auto_tac = auto_hyp_progress (fun _ _ -> true) backThruHypT
      }

(*
 * Quick test on assumptions.
 *)
let assum_test i p =
   let goal, assums = dest_msequent (Sequent.msequent p) in
   let goal = TermMan.nth_concl goal 0 in
   let assum = List.nth assums (i - 1) in
   let goal' = TermMan.nth_concl assum 0 in
      try match_terms [] goal' goal; true with
         RefineError _ ->
            false

let auto_resource =
   auto_resource.resource_improve auto_resource (**)
      { auto_name = "backThruSomeAssumT";
        auto_prec = back_assum_prec;
        auto_tac = auto_assum_progress assum_test backThruAssumT
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
