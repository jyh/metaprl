(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * State operations for FIR programs.
 *)

include Base_theory
include Itt_theory

derive Fir_state

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Interpret locations as integers. *)
(*
prim_rw unfold_first : first <--> 0
prim_rw unfold_next : next{ 'loc } <--> ('loc +@ 1)
*)

(* Location equality. *)
(*
prim_rw unfold_if_eq_loc :
   if_eq_loc{ 'loc1; 'loc2; 'e1; 'e2 } <-->
   ifthenelse{ beq_int{ 'loc1; 'loc2 }; 'e1; 'e2 }
*)

(* Derived rewrites. *)
interactive_rw reduce_if_eq_loc1 :
   if_eq_loc{ first; first; 'e1; 'e2 } <--> 'e1
interactive_rw reduce_if_eq_loc2 :
   if_eq_loc{ next{ 'loc }; first; 'e1; 'e2 } <--> 'e2
interactive_rw reduce_if_eq_loc3 :
   if_eq_loc{ first; next{ 'loc }; 'e1; 'e2 } <--> 'e2
interactive_rw reduce_if_eq_loc4 :
   if_eq_loc{ next{ 'loc1 }; next{ 'loc2 }; 'e1; 'e2 } <-->
   if_eq_loc{ 'loc1; 'loc2; 'e1; 'e2 }
