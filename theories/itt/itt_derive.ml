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

open Typeinf

open Itt_rfun
open Itt_logic
open Itt_struct

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
 * Similar elimination form.
 *)
interactive applyElim 'H 'J (z: 'A -> 'B['z]) 'y 'z :
   sequent [squash] { 'H; x: 'f 'a; 'J['x] >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'f 'a; 'J['x]; y: 'A >- "type"{'B['y]} } -->
   sequent [squash] { 'H; x: 'f 'a; 'J['x] >- 'a = 'a in 'A } -->
   sequent [squash] { 'H; x: 'f 'a; 'J['x] >- 'f = 'f in (z: 'A -> 'B['z]) } -->
   sequent [squash] { 'H; x: 'f 'a; 'J['x]; y: 'A; z: 'B['y] >- "type"{'z} } -->
   sequent ['ext] { 'H; x: 'f 'a; 'J['x]; y: 'B['a]; z: 'y >- 'C['z] } -->
   sequent ['ext] { 'H; x: 'f 'a; 'J['x] >- 'C['x] }

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

(*
 * Similar elimination form.
 *)
interactive independentApplyElim 'H 'J ('A -> 'B) 'y 'z :
   sequent [squash] { 'H; x: 'f 'a; 'J['x] >- "type"{'B} } -->
   sequent [squash] { 'H; x: 'f 'a; 'J['x] >- 'a = 'a in 'A } -->
   sequent [squash] { 'H; x: 'f 'a; 'J['x] >- 'f = 'f in ('A -> 'B) } -->
   sequent [squash] { 'H; x: 'f 'a; 'J['x]; z: 'B >- "type"{'z} } -->
   sequent ['ext] { 'H; x: 'f 'a; 'J['x]; y: 'B; z: 'y >- 'C['z] } -->
   sequent ['ext] { 'H; x: 'f 'a; 'J['x] >- 'C['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Search for an application that we can reduce.
 *)
let search_apply =
   let rec search goal p =
      if is_apply_term goal then
         let f, a = dest_apply goal in
            try
               let _, t = infer_type p f in
                  goal, t
            with
               RefineError _ ->
                  search_term goal p
      else
         search_term goal p
   and search_term goal p =
      let { term_op = op; term_terms = bterms } = dest_term goal in
         search_bterms bterms p
   and search_bterms bterms p =
      match bterms with
         bterm :: bterms ->
            begin
               try search (dest_bterm bterm).bterm p with
                  RefineError _ ->
                     search_bterms bterms p
            end
       | [] ->
            raise (RefineError ("search_apply", StringError "no applications found"))
   in
      search

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
         tac (hyp_count p) goal_type bind f a p
   else
      raise (RefineError ("d_applyT", StringError "no elimination form"))
(*
         let _, hyp = Sequent.nth_hyp p i in
         let t = get_type hyp in
         let j, k = Sequent.hyp_indices p i in
         let y, z = maybe_new_vars2 p "u" "v" in
         let tac =
            if is_fun_term t then
               independentApplyElim
            else
               applyElim
         in
            tac j k t y z p

let apply_term = << 'f 'a >>

let d_resource = d_resource.resource_improve d_resource (apply_term, d_applyT)
*)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
