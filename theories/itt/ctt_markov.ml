extends Itt_theory
extends Itt_nat

doc <:doc< @docoff >>

open Printf
open Mp_debug
open Refiner.Refiner
open Term
open TermOp
open TermMan
open TermSubst
open RefineError
open Term_stable
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Var

open Base_dtactic

open Itt_struct
open Itt_equal
open Itt_nat

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Ctt_markov%t"


interactive squash_stable1 'H 't :
   sequent [squash] { <H>; x:'T >- 't in 'T} -->
   sequent ['ext] { <H>; x:squash{'T} >- 'T}

interactive squash_stable2 'H bind{v.'t['v]} :
   sequent [squash] { <H>; v:squash{'T} >- 't['v] in 'T} -->
   sequent ['ext] { <H>; x:'T >- 't[it] in 'T}

interactive squash_ex1 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent ['ext]   { <H> >- squash{'A} => not{not{'A}} }

interactive squash_ex2 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent ['ext]   { <H> >- iff{squash{'A};squash{squash{'A}}} }

interactive squash_ex3 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- "type"{'B} } -->
   sequent ['ext]   { <H> >- iff{squash{.'A and 'B}; .squash{'A} and squash{'B}} }

interactive squash_ex4 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- "type"{'B} } -->
   sequent ['ext]   { <H> >- squash{.'A => 'B} => (squash{'A} => squash{'B}) }

interactive squash_ex5 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent ['ext]   { <H> >- iff{squash{not{'A}};not{squash{'A}}} }

interactive squash_ex6 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- "type"{'B} } -->
   sequent ['ext]   { <H> >- (squash{'A} or squash{'B}) => squash{.'A or 'B} }

define unfold_sqst : sqst{'A} <--> (squash{'A} => 'A)

dform sqst_df : except_mode[src] :: sqst{'A} =
    `"sqst(" slot["le"]{'A} `")"

interactive sqst_ex1 :
   sequent ['ext]   { <H> >- sqst{."false"} }

interactive sqst_ex2 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent ['ext]   { <H> >- sqst{.not{'A}} }

interactive sqst_ex3 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent ['ext]   { <H> >- sqst{.squash{'A}} }

interactive sqst_ex4 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- "type"{'B} } -->
   sequent ['ext]   { <H> >- (sqst{'A} and sqst{'B}) => sqst{.'A and 'B} }

interactive sqst_ex5 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- "type"{'B} } -->
   sequent ['ext]   { <H> >- (sqst{'B}) => sqst{.'A => 'B} }

prim markov :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent [squash] { <H> >- not{not{'A}} } -->
   sequent ['ext]   { <H> >- squash{'A} } =
   it

interactive markov3 : (* proved from Markov *)
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent ['ext]   { <H> >- squash{('A or  not{'A})} }

interactive markov1 'A : (* proved from Markov3 *)
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent [squash]   { <H>; x:'A >- 'B } -->
   sequent [squash]   { <H>; y:not{'A} >- 'B } -->
   [sqstable] sequent ['ext]   { <H>; v:squash{'B} >- 'B } -->
   sequent ['ext]   { <H> >- 'B }

interactive markov0 'A: (* proved from Markov1 *)
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent [squash]   { <H>; x:'A >- 't in 'T } -->
   sequent [squash]   { <H>; y:not{'A} >- 't in 'T } -->
   sequent ['ext]   { <H> >- 't in 'T }

interactive markov2' :(* = Markov, proved from Markov0 *)
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent [squash] { <H> >- not{not{'A}} } -->
   sequent ['ext]   { <H> >- squash{'A} }

interactive markovN : (* proved from Markov *)
   [wf] sequent [squash] { <H> >- 's in 'T } -->
   [wf] sequent [squash] { <H> >- 't in 'T } -->
   [main] sequent [squash] { <H> >- not{not{.'s='t in 'T}} } -->
   sequent ['ext] { <H> >- 's='t in 'T }

interactive markov2 : (*  = Markov, proved from MarkovN *)
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent [squash] { <H> >- not{not{'A}} } -->
   sequent ['ext]   { <H> >- squash{'A} }

interactive markov4 {| intro [SelectOption 1] |} : (*  = proved from Markov *)
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent [squash] { <H>; x:not{'A} >- "false" } -->
   sequent ['ext]   { <H> >- squash{'A} }

interactive markov2'' : (*  = Markov, proved from Markov4 *)
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent [squash] { <H> >- not{not{'A}} } -->
   sequent ['ext]   { <H> >- squash{'A} }

interactive markovPrinciple :
   [wf] sequent [squash] { <H>; n:nat >- "type"{.'A 'n} } -->
   sequent ['ext]   { <H> >- all n:nat. ('A 'n or  not{.'A 'n}) =>
                           not{not{.exst n:nat.'A 'n}} =>
                           exst n:nat.'A 'n}

   (* Proof uses f =  fix{f.lambda{n.decide{('x 'n);a.('n,'a);b.'f ('n+@1)}}} *)


interactive squash_ex4m :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- "type"{'B} } -->
   sequent ['ext]   { <H> >- (squash{'A} => squash{'B}) => squash{.'A => 'B} }


interactive sqst_ex6 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent ['ext]   { <H> >- sqst{'A} => not{not{'A}} =>'A }


define unfold_delta: delta{'A} <--> (quot x,y:'A//"true")

dform delta_df : except_mode[src] :: delta{'A} =
   Nuprl_font!Delta slot["le"]{'A}

interactive delta1 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent ['ext]   { <H> >- ('A => delta{'A}) }

interactive delta2 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent ['ext]   { <H> >- (delta{'A} => squash{'A}) }



