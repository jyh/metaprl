doc <:doc<
   @module[Itt_unit2]
   Simple facts about disjoint union.
>>
extends Itt_bool
extends Itt_isect (* top *)

open Dtactic
open Top_conversionals

define is_inl: is_inl{'t} <--> decide{'t; x.btrue; y.bfalse}
define is_inr: is_inr{'t} <--> decide{'t; y.bfalse; x.btrue}

let resource reduce +=
[ <<is_inl{inl{'t}}>>, (is_inl thenC reduceTopC);
  <<is_inl{inr{'t}}>>, (is_inl thenC reduceTopC);
  <<is_inr{inl{'t}}>>, (is_inr thenC reduceTopC);
  <<is_inr{inr{'t}}>>, (is_inr thenC reduceTopC)]

interactive inl_wf {| intro[] |}:
   sequent { <H> >- 't in top+top } -->
   sequent { <H> >- is_inl{'t} in bool }

interactive inr_wf {| intro[] |}:
   sequent { <H> >- 't in top+top } -->
   sequent { <H> >- is_inr{'t} in bool }
