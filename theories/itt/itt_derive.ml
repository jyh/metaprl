(*
 * These are some extra derived rules to make proofs easier.
 *)

include Itt_fun
include Itt_prod
include Itt_struct
include Itt_logic

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Sequent
open Var
open Nltop

open Typeinf

open Itt_rfun
open Itt_logic
open Itt_struct
open Itt_equal

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * To prove an application,
 * Show that the function is family of types,
 * and the argument is an index.
 *)
interactive applyIntro 'H (x: 'A -> 'B['x]) (bind{y. 'C['y]}) 'f 'a :
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent [squash] { 'H >- 'f = 'f in (x: 'A -> 'B['x]) } -->
   sequent [squash] { 'H >- "type"{'B['a]} } -->
   sequent [squash] { 'H; y: 'B['a] >- "type"{'C['y]} } -->
   sequent ['ext] { 'H; y: 'B['a] >- 'C['y] } -->
   sequent ['ext] { 'H >- 'C['f 'a] }

(*
 * To prove an application,
 * Show that the function is family of types,
 * and the argument is an index.
 *)
interactive independentApplyIntro 'H ('A -> 'B) (bind{y. 'C['y]}) 'f 'a :
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent [squash] { 'H >- 'f = 'f in ('A -> 'B) } -->
   sequent [squash] { 'H; y: 'B >- "type"{'C['y]} } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H; y: 'B >- 'C['y] } -->
   sequent ['ext] { 'H >- 'C['f 'a] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Add them as resources.
 *)
let applyT app i p =
   if i = 0 then
      let f, a = dest_apply app in
      let goal_type =
         try get_with_arg p with
            RefineError _ ->
               snd (infer_type p f)
      in
      let goal_type, tac =
         if is_dfun_term goal_type then
            goal_type, applyIntro
         else if is_all_term goal_type then
            let v, a, b = dest_all goal_type in
               mk_dfun_term v a b, applyIntro
         else if is_fun_term goal_type then
            goal_type, independentApplyIntro
         else if is_implies_term goal_type then
            let a, b = dest_implies goal_type in
               mk_fun_term a b, independentApplyIntro
         else
            raise (RefineError ("d_applyT", StringTermError ("not a function type", goal_type)))
      in
      let v = maybe_new_vars1 p "v" in
      let bind = mk_bind_term v (var_subst (Sequent.concl p) app v) in
         (tac (hyp_count p) goal_type bind f a
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
   else
      raise (RefineError ("d_applyT", StringError "no elimination form"))

(*
 * Search for an application that we can reduce.
 * In this heuristic, we don't descend into the type in equalities.
 *)
let add_term app apps =
   let rec search app = function
      app' :: apps ->
         if alpha_equal app app' then
            true
         else
            search app apps
    | [] ->
         false
   in
      if search app apps then
         apps
      else
         app :: apps

let search_apply =
   let rec search apps vars goal =
      if is_apply_term goal then
         let f, a = dest_apply goal in
            if is_var_term f & List.mem (dest_var f) vars then
               search_term (add_term goal apps) vars goal
            else
               search_term apps vars goal
      else
         search_term apps vars goal
   and search_term apps vars goal =
      let { term_op = op; term_terms = bterms } = dest_term goal in
         if is_equal_term goal then
            search_bterms apps vars (List.tl bterms)
         else
            search_bterms apps vars bterms
   and search_bterms apps vars = function
      bterm :: bterms ->
         let apps = search apps vars (dest_bterm bterm).bterm in
            search_bterms apps vars bterms
    | [] ->
         apps
   in
      search []

(*
 * Search for a possible application in the conclusion.
 * This is quite heuristic.  We don't descend into
 * the types for equalities.
 *)
let rec anyApplyT apps i p =
   match apps with
      [app] ->
         applyT app i p
    | app :: apps ->
         (applyT app i orelseT anyApplyT apps i) p
    | [] ->
         raise (RefineError ("anyApplyT", StringError "no applications found"))

let autoApplyT i p =
   let goal = Sequent.concl p in
      if is_type_term goal then
         raise (RefineError ("autoApplyT", StringError "don't apply to 'type' goals"))
      else
         let vars = Sequent.declared_vars p in
         let apps =
            if i = 0 then
               search_apply vars (Sequent.concl p)
            else
               let _, hyp = Sequent.nth_hyp p i in
                  search_apply vars hyp
         in
            anyApplyT apps i p

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
