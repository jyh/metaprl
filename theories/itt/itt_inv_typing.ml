extends Itt_disect
extends Itt_prod
extends Itt_dfun

open Itt_struct
open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals

open Base_auto_tactic
open Base_dtactic

prim dintersectionTypeElimination {| elim [ThinOption thinT] |} 'H 'a :
   [wf] sequent [squash] { <H>; u:"type"{.bisect{'A; x. 'B['x]}}; <J['u]>  >- 'a in 'A } -->
   ('t['u;'v] :
   sequent ['ext] { <H>; u:"type"{.bisect{'A; x. 'B['x]}}; v:"type"{'B['a]}; <J['u]> >- 'C['u] }) -->
   sequent ['ext] { <H>; u:"type"{.bisect{'A; x. 'B['x]}}; <J['u]> >- 'C['u] } =
   't['u;it]

prim independentProductTypeElimination {| elim [ThinOption thinT] |} 'H :
   ('t['u;'v;'w] :
   sequent ['ext] { <H>; u:"type"{.'A * 'B}; v:"type"{'A}; w:"type"{'B}; <J['u]> >- 'C['u] }) -->
   sequent ['ext] { <H>; u:"type"{.'A * 'B}; <J['u]> >- 'C['u] } =
   't['u;it;it]

prim functionTypeElimination {| elim [ThinOption thinT] |} 'H :
   ('t['u;'v; 'w] :
   sequent ['ext] { <H>; u:"type"{. 'A -> 'B }; v:"type"{'A}; w:('A -> "type"{'B}); <J['u]> >- 'C['u] }) -->
   sequent ['ext] { <H>; u:"type"{. 'A -> 'B }; <J['u]> >- 'C['u] } =
   't['u;it;it]

