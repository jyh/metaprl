(*
 * Typehood in FOL.
 *)

include Base_theory

(*
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

open Mp_resource
open Tacticals
open Base_auto_tactic
*)

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare univ
declare prop{'t}
declare "type"{'A}
declare trivial

(*
dform type_df : "type"{'A} = slot{'A} `" type"
dform trivial_df : trivial = cdot
dform univ_df : univ = `"Univ"
dform prop_df : prop{'t} = downarrow slot{'t}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim univ_type 'H 'J : :
   sequent ['ext] { 'H; x: univ; 'J['x] >- "type"{prop{'x}} } =
   trivial

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Automation.  Add a search tactic to trivialT.
 *)
let nthUnivT i p =
   let j, k = Sequent.hyp_indices p i in
      univ_type j k p

let trivial_resource =
   trivial_resource.resource_improve trivial_resource (**)
      { auto_name = "nthUnivT";
        auto_prec = trivial_prec;
        auto_tac = onSomeHypT nthUnivT
      }

let type_term = << "type"{'A} >>
let type_opname = opname_of_term type_term
let is_type_term = is_dep0_term type_opname
let mk_type_term = mk_dep0_term type_opname
let dest_type = dest_dep0_term type_opname
*)

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
