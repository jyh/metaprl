(*
 * Display all the elements in a particular theory.
 *)

include Itt_theory

open Printf
open Nl_debug

open Refiner.Refiner.Refine

open Resource

open Tacticals
open Conversionals

open Itt_rfun
open Itt_bool
open Itt_int
open Itt_int_bool

declare fact{'i}

primrw reduceFact : fact{'i} <--> fix{f. lambda{i. ifthenelse{eq_int{'i; 0}; 1; .'i *@ 'f ('i -@ 1)}}} 'i

dform fact_df : parens :: "prec"[prec_apply] :: fact{'i} =
   `"fact" " " slot{'i}

let redexC =
   firstC [reduceBeta;
           reduceEQInt;
           reduceFact;
           reduceBoolTrue;
           reduceBoolFalse;
           reduceIfthenelseTrue;
           reduceIfthenelseFalse;
           reduceAdd;
           reduceSub;
           reduceMul;
           reduceDiv;
           reduceFix]

let goal = mk_msequent << sequent { 'H >- fact{300} = 0 in int } >> []

(*
let cache = Tactic_cache.extract (cache_resource.resource_extract cache_resource)

let arg =
   Sequent.create (**)
      any_sentinal      (* Sentinal *)
      "main"            (* Label *)
      goal              (* Goal of proof *)
      cache             (* Proof cache *)
      []                (* Attributes *)

let test () =
   let subgoals, ext = Tacticals.refine (timingT (rw (repeatC (higherC redexC)) 0)) arg in
      match subgoals with
         [subgoal] ->
            Simple_print.SimplePrint.print_simple_term (Sequent.goal subgoal);
            eflush stdout
       | [] ->
            eprintf "No subgoals%t" eflush
       | _ ->
            eprintf "Too many subgoals%t" eflush
*)


(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.top"
 * End:
 * -*-
 *)
