(*
 * Display all the elements in a particular theory.
 *)

include Itt_theory

open Refiner.Refiner.Refine

open Resource

open Tactic_type
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

let resources =
   { ref_d = d_resource.resource_extract d_resource;
     ref_eqcd = eqcd_resource.resource_extract eqcd_resource;
     ref_typeinf = typeinf_resource.resource_extract typeinf_resource;
     ref_squash = squash_resource.resource_extract squash_resource;
     ref_subtype = sub_resource.resource_extract sub_resource
   }

let goal = { mseq_hyps = []; mseq_goal = << sequent { 'H >- fact{40} = 0 in int } >> }

let cache = Tactic_cache.extract (cache_resource.resource_extract cache_resource)

let arg =
   Tactic_type.create (**)
      "main"            (* Label *)
      goal              (* Goal of proof *)
      cache             (* Proof cache *)
      []                (* Attributes *)
      resources

let test () =
   let subgoals, ext = Tactic_type.refine (rw (repeatC (higherC redexC)) 0) arg in
      ()

(*
 * $Log$
 * Revision 1.1  1998/06/16 16:26:11  jyh
 * Added itt_test.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.top"
 * End:
 * -*-
 *)
