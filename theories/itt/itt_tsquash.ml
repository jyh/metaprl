extends Itt_isect
extends Itt_set
extends Itt_struct

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Var

open Dtactic

open Itt_struct

define unfold_tsquash : tsquash{'A} <--> ({ x:top | 'A})

interactive tsquashEquality {| intro [] |}  :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   sequent { <H> >- tsquash{'A1} = tsquash{'A2} in univ[i:l] }

interactive tsquashType {| intro [] |} :
   sequent{ <H> >- "type"{'A}} -->
   sequent { <H> >- "type"{tsquash{'A}}}

interactive tsquashMemberEquality {| intro [] |} :
   sequent{ <H> >- squash{'A}} -->
   sequent { <H> >- 'x='y in tsquash{'A}}

interactive tsquashMemberFormation {| intro [] |} :
   sequent{ <H> >- squash{'A}} -->
   sequent { <H> >- tsquash{'A}}

interactive tsquashElimination {| elim [ThinOption thinT] |} 'H :
   sequent{ <H>; u:top; x: squash{'A}; <J['u]> >- 'C['u]} -->
   sequent{ <H>; u:tsquash{'A}; <J['u]> >- 'C['u]}


dform tsquash_df : except_mode[src] :: tsquash{'A} = `"[" slot{'A} `"]" Nuprl_font!subt


