doc <:doc< 
   @begin[doc]
   @module[Itt_datatree]
  
   This is a theory of binary trees with data.
   @end[doc]
>>

extends Itt_bintree
extends Itt_record
extends Itt_logic

doc <:doc< @docoff >>

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
open Base_dtactic
open Tactic_type.Conversionals

open Base_auto_tactic

open Itt_logic
open Itt_record
open Itt_bintree


(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_datatree%t"



doc <:doc< 
   @begin[doc]
   @modsection{Definition}
   @end[doc]
>>

define bindatatree : DataTree{'A} <--> BinTree{{"data":'A}}

dform dt_df : except_mode[src] :: DataTree{'A} = `"DataTree(" 'A ")"


interactive datatree_wf {| intro[] |} :
 sequent[squash]{ <H> >-"type"{ 'A}} -->
 sequent['ext]  { <H> >-"type"{ DataTree{'A}}}

interactive datatree_subtype {| intro[] |} :
 sequent[squash]{ <H> >-"type"{ 'A}} -->
 sequent['ext]  { <H> >-"subtype"{ DataTree{'A};BinTree}}


doc <:doc< 
   @begin[doc]
   @modsection{Set of elements}
    A data tree is defined as set of elements.

  First let us define whether an element is in a tree:
   @end[doc]
>>


define in_tree: in_tree{'a;'t; 'A} <--> tree_ind{ 't;  ."false"; L,R,self. 'L or 'R or 'a = ^data in 'A}

dform in_tree_df : except_mode[src] ::  in_tree{'a;'t; 'A} = 'a Nuprl_font!member 't Nuprl_font!member DataTree{'A}


interactive_rw in_tree_base:  in_tree{'a; emptytree; 'A} <--> "false"
interactive_rw in_tree_step:  in_tree{'a; tree{'node}; 'A} <--> ( in_tree{'a;.'node^left;'A} or in_tree{'a;.'node^right;'A} or 'a = 'node^data in 'A)

let resource reduce +=
   [<<  in_tree{'a; emptytree; 'A}   >>, in_tree_base;
    <<  in_tree{'a; tree{'node}; 'A}  >>, in_tree_step
   ]


(* in_tree is a proposition *)

interactive in_tree_wf {| intro[] |} :
 sequent[squash]{ <H> >- 'a in  'A} -->
 sequent[squash]{ <H> >- 't in DataTree{'A} } -->
 sequent['ext]  { <H> >- "type"{in_tree{'a;'t; 'A}} }

interactive in_tree_univ {| intro[] |} :
 sequent[squash]{ <H> >- 'A in  univ[i:l]} -->
 sequent[squash]{ <H> >- 'a in  'A} -->
 sequent[squash]{ <H> >- 't in DataTree{'A} } -->
 sequent['ext]  { <H> >- in_tree{'a;'t; 'A} in univ[i:l] }


doc <:doc< 
   @begin[doc]
   Now we can define set of elements of the tree:
   @end[doc]
>>



define set_from_tree: set_from_tree{'t;'A} <--> {a:'A |  in_tree{'a;'t; 'A}}

dform dt_df : except_mode[src] ::  set_from_tree{'t;'A} = `"|" 't `"|" sub{'A}


interactive set_from_tree_wf {| intro[] |} :
 sequent[squash]{ <H> >- "type"{'A}} -->
 sequent[squash]{ <H> >- 't in DataTree{'A} } -->
 sequent['ext]  { <H> >- "type"{set_from_tree{'t;'A}} }

interactive set_from_tree_univ {| intro[] |} :
 sequent[squash]{ <H> >- 'A in univ[i:l]} -->
 sequent[squash]{ <H> >- 't in DataTree{'A} } -->
 sequent['ext]  { <H> >- set_from_tree{'t;'A} in univ[i:l]}

interactive set_from_tree_subtype {| intro[] |} :
 sequent[squash]{ <H> >- "type"{'A}} -->
 sequent[squash]{ <H> >- 't in DataTree{'A} } -->
 sequent['ext]  { <H> >- "subtype"{set_from_tree{'t;'A}; 'A} }


(* ==================== *)


doc <:doc< 
   @begin[doc]
   @modsection{Examples}
   @end[doc]
>>


interactive example_wf2 {| intro[] |} :
 sequent['ext]  { <H> >- simpletree in DataTree{int} }


interactive example_19 {| intro[] |} :
 sequent['ext]  { <H> >- in_tree{19; simpletree; int} }


