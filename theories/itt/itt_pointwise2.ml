doc <:doc< 
 @begin[doc]
 @module[Itt_pointwise2]
 @end[doc]
>>

extends Itt_equal
extends Itt_quotient
extends Itt_struct
extends Itt_tunion
extends Itt_bunion
extends Itt_pointwise
doc <:doc< @docoff >>

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Var
open Mptop

open Auto_tactic

open Dtactic

open Itt_equal
open Itt_struct
open Itt_quotient

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_pointwise2%t"

(* debug_string DebugLoad "Loading itt_struct..." *)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc< 
 @begin[doc]
  The following rules are derived only in pointwise functionality.
   They both contradict to Let rule.
 @end[doc]
>>


interactive quotientElimination2 {| elim [ThinOption thinT] |} 'H :
   [wf] sequent [squash] { <H>; a: quot x, y: 'A // 'E['x; 'y]; <J['a]> >- "type"{'T['a]} } -->
   [main] sequent [squash] { <H>; a: quot x, y: 'A // 'E['x; 'y];
             v: 'A; w: 'A; z: 'E['v; 'w]; <J['v]> >- 's['v] = 't['w] in 'T['v]
           } -->
   sequent ['ext] { <H>; a: quot x, y: 'A // 'E['x; 'y]; <J['a]> >- 's['a] = 't['a] in 'T['a] }


interactive tunionElimination2 {| elim [ThinOption thinT] |} 'H :
   sequent [squash] { <H>; z: tunion{'A; y. 'B['y]};  w: 'A; x: 'B['w]; <J['x]> >- squash{'C['x]}  } -->
   sequent ['ext] { <H>; x: tunion{'A; y. 'B['y]}; <J['x]> >- squash{'C['x]} }

interactive bunionElimination2 {| elim [ThinOption thinT] |} 'H :
   [main] sequent [squash] { <H>; x: 'A; <J['x]> >- squash{'C['x]} } -->
   [main] sequent [squash] { <H>; x: 'B; <J['x]> >- squash{'C['x]} } -->
   sequent ['ext] { <H>; x: 'A bunion 'B; <J['x]> >- squash{'C['x]} }


doc <:doc< @docoff >>
