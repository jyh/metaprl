doc <:doc<
   @begin[doc]
   @module[Itt_reflection]

   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2004 MetaPRL Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_theory
extends Base_reflection
extends Itt_nat
doc docoff


open Dtactic

open Base_reflection
open Basic_tactics
open Itt_nat
open Itt_equal
open Itt_struct
open Itt_squash

(************************************************************************
 * The BTerm type                                                       *
 ************************************************************************)

define unfold_is_bterm: is_bterm{'bt} <--> Base_reflection!if_bterm{'bt;"true"}

dform isbterm_df : except_mode[src] :: is_bterm{'bt} =
   `"is_bterm(" slot{'bt} `")"

let resource reduce +=
   (<<is_bterm{ bterm{| <H> >- 't |} }>>, (unfold_is_bterm thenC reduce_ifbterm))


dform ifbterm_df : except_mode[src] :: if_bterm{'bt; 'P} =
   `"ifbterm(" slot{'bt} `";" slot{'P} `")"

prim_rw ifbterm_reduce {| reduce |} :
   ( is_bterm{'b} ) -->
   if_bterm{'b; 'P} <--> 'P

interactive ifbterm_type {| intro [] |} :
   sequent { <H> >- 'P Type} -->
   sequent { <H> >- is_bterm{'b} } -->
   sequent { <H> >- if_bterm{'b; 'P} Type }

interactive ifbterm_intro {| intro [] |} :
   sequent { <H> >- is_bterm{'b} } -->
   sequent { <H> >- 'P } -->
   sequent { <H> >- if_bterm{'b; 'P} }


declare BTerm

dform bterm_df : except_mode[src] :: BTerm =
   `"BTerm"

prim btermEquality {| intro [] |} :
   sequent { <H> >- BTerm in univ[i:l] } =
   it

interactive btermType {| intro [] |} :
   sequent { <H> >- BTerm Type }

prim bterm_memberEquality {| intro [AutoMustComplete] |} :
   sequent { <H> >- is_bterm{'x<||>} } -->
   sequent { <H> >- 'x<||> in BTerm } =
   it

prim btermSquiddle {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'b1 = 'b2 in BTerm } -->
   sequent { <H> >- 'b1 ~ 'b2 } =
   it

(*
 * XXX: TODO: we use bterm{| >- term[@] |} a lot, we should have a definition
 * with a shorter name for it. Also, "term" is probably not the best operator,
 * "it" might be a better choice. (possible names: itterm or itbterm)
 *)

interactive term_is_bterm {| intro [] |} :
   sequent { <H> >- bterm{| >- term[@] |} in BTerm }

interactive btermFormation {| intro [] |} :
   sequent { <H> >- BTerm }

(************************************************************************
 * Subterms                                                             *
 ************************************************************************)

declare list_of_xlist{'l}

prim_rw reduce_xlist_cons :
   list_of_xlist{ (Perv!cons{'hd; 'tl})} <--> ('hd :: list_of_xlist{'tl})

prim_rw reduce_xlist_nil :
   list_of_xlist{ (Perv!nil) } <--> nil

let rec reduce_xlist t =
   if is_xnil_term (one_subterm t) then
      reduce_xlist_nil
   else reduce_xlist_cons thenC addrC [1] (termC reduce_xlist)


define unfold_subterms:
   subterms{'t} <--> list_of_xlist{ (Base_reflection!subterms{'t}) }

dform list_of_xlist_df : except_mode[src] :: list_of_xlist{'l} =
   `"list_of_xlist(" slot{'l} `")"

dform subterms_df : except_mode[src] :: subterms{'bt} =
   `"subterms(" slot{'bt} `")"

let reduce_subterms =
   unfold_subterms thenC addrC [0] Base_reflection.reduce_subterms thenC termC reduce_xlist

let resource reduce +=
   ( << subterms{ bterm{| <H> >- 't |} } >>, reduce_subterms )

(* XXX: BUG: subterms is currently undefined on variables *)
prim subterms_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
(* sequent { <H> >- not var_term{'bt} } --> *)
   sequent { <H> >- subterms{'bt} in list{BTerm} } =
   it

(*
 * XXX: TODO: instead of having separate conditions for 'bt in BTerm and
 * not var_term{'bt} we might want to define a type { bt: BTerm |  not var_term{'bt} }
 * and use that one in all the relevant places. (possible name - OpBTerm)
 *)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of bterm and subterms of bterms.
 *)
let resource typeinf += (<< BTerm >>, infer_univ1)
let resource typeinf += (<< subterms{'bt} >>, infer_const << list{BTerm} >>)



(************************************************************************
 * Make_bterm                                                           *
 ************************************************************************)

declare xlist_of_list{'l}

prim_rw xlist_list_cons {| reduce |} :
   xlist_of_list{ 'hd :: 'tl } <--> Perv!cons{'hd; xlist_of_list{'tl}}

prim_rw xlist_list_nil {| reduce |} :
   xlist_of_list{ nil } <--> (Perv!nil)


define unfold_make_bterm : make_bterm{'bt; 'bt_list} <--> Base_reflection!make_bterm{'bt; xlist_of_list{'bt_list}}

dform make_bterm_df : except_mode[src] :: make_bterm{'bt; 'btl} =
   `"make_bterm(" slot{'bt} `"; " slot{'btl} `")"

let resource reduce +=
   ( << make_bterm{ bterm{| <H> >- 't |}; 'btl } >>, (unfold_make_bterm thenC reduceC) )

(* XXX: BUG: need extra conditions *)
prim makebterm_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
(* sequent { <H> >- not var_term{'bt} } --> *)
   sequent { <H> >- 'btl in list{BTerm} } -->
(* sequent { <H> >- compatible_shapes{'btl; subterms{'bt}} } --> *)
   sequent { <H> >- make_bterm{'bt; 'btl} in BTerm } =
   it

(*
 * Rough draft of definitions:
 *
 * are_compatible_shapes{l1; l2} <-->\
 *   list_ind{l1, is_nil{l2}, hd1,tl1,_.list_ind{l2,bfalse, hd2,tl2,_. are_same_shapes_aux{var_arity{hd2} -@ var_arity{hd1}, tl1, tl2}}}}
 *
 * (definition below is recursive, need to use "fix" or similar)
 * are_compatible_shapes_aux{diff, l1, l2} <-->
 *   list_ind{l1, is_nil{l2}, hd1,tl1,_.list_ind{l2,bfalse, hd2,tl2,_.
 *      ((var_arity{hd2} -@ var_arity{hd1}) =_int diff) band are_compatible_shapes_aux{diff, tl1, tl2}}}}
 *
 * compatible_shapes{l1; l2} <--> "assert"{are_same_shapes{l1; l2}}
 *
 * Note: instead of using compatible_shapes{'btl; subterms{'bt}} we might want to define compatible_shapes{'bt; 'btl}
 * (making the "subterms" operator a part of the definition instead of a part of each rule)
 *)

(************************************************************************
 * Same_op                                                              *
 ************************************************************************)

define unfold_is_same_op: is_same_op{'b1; 'b2} <--> if_same_op{'b1; 'b2; "btrue"; "bfalse"}

define unfold_same_op: same_op{'b1; 'b2} <--> "assert"{is_same_op{'b1; 'b2}}

dform sameop_df : except_mode[src] :: same_op{'b1; 'b2} =
   `"same_op(" slot{'b1} `"; " slot{'b2} `")"

(* XXX: TODO: needs to be updated *)
let resource reduce +=
   (<< same_op{ bterm{| <H1> >- 't1 |}; bterm{| <H2> >- 't2 |} } >>,
   (unfold_same_op thenC Base_reflection.reduce_if_same_op))

prim is_same_op_wf {| intro [] |} :
   sequent { <H> >- 'b1 in BTerm } -->
   sequent { <H> >- 'b2 in BTerm } -->
   sequent { <H> >- is_same_op{'b1; 'b2} in bool } =
   it

interactive same_op_wf {| intro [] |} :
   sequent { <H> >- 'b1 in BTerm } -->
   sequent { <H> >- 'b2 in BTerm } -->
   sequent { <H> >- same_op{'b1; 'b2} Type }

prim same_op_id {| intro [] |} :
   sequent { <H> >- 'b in BTerm } -->
   sequent { <H> >- same_op{'b; 'b} } =
   it

interactive same_op_id2 {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'b1 = 'b2 in BTerm } -->
   sequent { <H> >- same_op{'b1; 'b2} }

prim_rw makebterm_same_op :
   'b1 in BTerm -->
   'b2 in BTerm -->
   same_op{'b1; 'b2} -->
   make_bterm{'b1; subterms{'b2}} <--> 'b2

interactive_rw makebterm_reduce {| reduce |} :
   'b in BTerm -->
    make_bterm{'b; subterms{'b}} <--> 'b

(************************************************************************
 * Simple_bterm                                                         *
 ************************************************************************)

define unfold_is_simple_bterm: is_simple_bterm{'bt} <--> if_simple_bterm{'bt; btrue; bfalse}
define unfold_simple_bterm: simple_bterm{'bt} <--> "assert"{is_simple_bterm{'bt}}

dform is_simple_bterm_df : except_mode[src] :: is_simple_bterm{'bt} =
   `"is_simple_bterm(" slot{'bt} `")"
dform simple_bterm_df : except_mode[src] :: simple_bterm{'bt} =
   `"simple_bterm(" slot{'bt} `")"

let is_simple_reduce = unfold_is_simple_bterm thenC Base_reflection.reduce_if_simple_bterm
let simple_reduce = unfold_simple_bterm thenC addrC [0] is_simple_reduce

let resource reduce +=
   [ << is_simple_bterm{ bterm{| <H1> >- 't1 |} } >>, is_simple_reduce;
     << simple_bterm{ bterm{| <H1> >- 't1 |} } >>, simple_reduce ]


prim is_simple_bterm_bool {| intro [] |} :
   [wf] sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- is_simple_bterm{'bt} in bool } =
   it

interactive_rw simple_is_simple :
   (simple_bterm{ 'bt}) -->
   is_simple_bterm{'bt} <--> btrue

interactive_rw notsimple_is_not_simple :
   ('bt in BTerm ) -->
   (not{simple_bterm{ 'bt}} ) -->
   is_simple_bterm{'bt} <--> bfalse

interactive simple_bterm_univ {| intro [] |} :
   [wf] sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- simple_bterm{'bt} in univ[i:l] }

interactive simple_bterm_type {| intro [] |} :
   [wf] sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- simple_bterm{'bt} Type }

interactive simple_bterm_decidable {| intro [] |} :
   [wf] sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- decidable{simple_bterm{'bt}} }

interactive term_is_simplebterm {| intro [] |} :
   sequent { <H> >- simple_bterm{ bterm{| >- term[@] |} } }

(************************************************************************
 * The Term type.                                                       *
 ************************************************************************)

define unfold_term: Term <--> { b: BTerm | simple_bterm{'b} }

dform term_df : except_mode[src] :: Term =
   `"Term"

interactive termEquality {| intro [] |} :
   sequent { <H> >- Term in univ[i:l] }

interactive termType {| intro [] |} :
   sequent { <H> >- Term Type }

interactive term_memberEquality {| intro [] |} :
   sequent { <H> >- 'x = 'y in BTerm } -->
   sequent { <H> >- simple_bterm{'x} } -->
   sequent { <H> >- 'x = 'y in Term }

interactive termElimination {| elim [] |} 'H :
   sequent { <H>; b: BTerm; u: simple_bterm{'b}; <J['b]> >- 'C['b] } -->
   sequent { <H>; b: Term; <J['b]> >- 'C['b] }

interactive term_in_term {| intro [] |} :
   sequent { <H> >- bterm{| >- term[@] |} in Term }


(************************************************************************
 * Var_bterm                                                            *
 ************************************************************************)

(*
 * XXX: TODO: for consistency, we should define is_var_bterm that maps to booleans and
 * then define var_bterm as assert of is_var_bterm
 *)

define unfold_var_bterm: var_bterm{'bt} <--> Base_reflection!if_var_bterm{'bt; "true"; "false"}

dform var_bterm_df : except_mode[src] :: var_bterm{'bt} =
   `"var_bterm(" slot{'bt} `")"

let resource reduce +=
   (<< var_bterm{ bterm{| <H1> >- 't1 |} } >>, (unfold_var_bterm thenC Base_reflection.reduce_if_var_bterm))

prim var_bterm_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- var_bterm{'bt} Type } =
   it

define unfold_is_var_bterm: is_var_bterm{'bt} <-->  Base_reflection!if_var_bterm{'bt; btrue; bfalse}

let resource reduce +=
   (<< is_var_bterm{ bterm{| <H1> >- 't1 |} } >>, (unfold_is_var_bterm thenC Base_reflection.reduce_if_var_bterm))

interactive is_var_bterm_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- is_var_bterm{'bt} in bool }


define unfold_Var: Var <--> { bt:BTerm | var_bterm{'bt} }

interactive var_wf {| intro [] |} :
   sequent { <H> >- Var Type }

interactive var_subtype {| intro [] |} :
   sequent { <H> >- Var subtype BTerm }

interactive_rw var_is_var:
   ('v in Var) -->
   is_var_bterm{'v} <--> btrue

(* XXX: BUG: need extra conditions *)
prim make_bterm_is_not_var {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
(* sequent { <H> >- not var_term{'bt} } --> *)
   sequent { <H> >- 'btl in list{BTerm} } -->
(* sequent { <H> >- compatible_shapes{'btl; subterms{'bt}} } --> *)
   sequent { <H> >-  not{var_bterm{ make_bterm{'bt; 'btl} }} } =
   lambda{x.'x}

(* XXX: TODO: prove an elimination form of the above *)

(************************************************************************
 * Subst                                                                *
 ************************************************************************)

define unfold_subst: subst{'bt; 't} <--> Base_reflection!subst{'bt; 't}

dform subst_df : except_mode[src] :: subst{'bt; 't} =
   `"subst(" slot{'bt} `"; " slot{'t} `")"

let resource reduce +=
   (<< subst{ bterm{| <H1> >- 't1 |}; bterm{| >- 't2 |} } >>, (unfold_subst thenC Base_reflection.reduce_subst))

prim subst_wf1 {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'bt1 = 'bt2 in BTerm } -->
   sequent { <H> >- not{simple_bterm{'bt1}} } -->
   sequent { <H> >- 't1 ='t2 in Term } -->
   sequent { <H> >- subst{'bt1; 't1} = subst{'bt2; 't2} in BTerm } =
   it

(************************************************************************
 * Var_arity                                                            *
 ************************************************************************)

define unfold_var_arity: var_arity{'t} <-->
   fix{ f. lambda{ b.
             if is_simple_bterm{'b}
               then 0
               else 1 +@ ('f subst{'b; bterm{| >- term[@] |}})
        } } 't

dform var_arity_df : except_mode[src] :: var_arity{'t} =
   `"var_arity(" slot{'t} `")"

let fold_var_arity = makeFoldC << var_arity{'t} >> unfold_var_arity

interactive_rw var_arity_not_simple :
   ( 'b in BTerm ) -->
   (not{simple_bterm{'b}}) -->
   var_arity{'b} <--> 1 +@ var_arity{subst{'b; bterm{| >- term[@] |}}}

interactive_rw var_arity_simple :
  (simple_bterm{'b}) -->
   var_arity{'b} <--> 0

(* XXX: TODO: We need to decide if we want bterm{| >- ... |} to be a no-op instead *)
interactive_rw var_arity_reduce_simple :
   var_arity{bterm{| >- 'b |}} <--> 0

interactive_rw var_arity_reduce_not_simple {| reduce |}:
   var_arity{bterm{| x:term; <H> >- 'b['x] |}} <-->
       1 +@ var_arity{ bterm{| <H> >- 'b[ term[@] ] |} }

prim var_arity_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- var_arity{'bt} in nat } =
   it

prim var_arity_subst {| intro [] |} :
   sequent { <H> >- 'b in BTerm } -->
   sequent { <H> >- not{simple_bterm{'b}} } -->
   sequent { <H> >- 'a1 in Term } -->
   sequent { <H> >- 'a2 in Term } -->
   sequent { <H> >- var_arity{subst{'b; 'a1}} ~ var_arity{subst{'b; 'a2}} } =
   it

interactive var_arity_wf2 {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- var_arity{'bt} in int }

interactive var_arity_subst1 {| intro [] |} :
   sequent { <H> >- 'b in BTerm } -->
   sequent { <H> >- not{simple_bterm{'b}} } -->
   sequent { <H> >- 'a in Term } -->
   sequent { <H> >- var_arity{'b} = 1 +@ var_arity{subst{'b; 'a}} in nat }

interactive var_arity_subst2 {| intro [] |} :
   sequent { <H> >- 'b in BTerm } -->
   sequent { <H> >- not{simple_bterm{'b}} } -->
   sequent { <H> >- 'a in Term } -->
   sequent { <H> >- var_arity{subst{'b; 'a}} < var_arity{'b} }

(************************************************************************
 * Subterms_arity                                                       *
 ************************************************************************)

define unfold_subterms_arity: subterms_arity{'bt} <--> length{subterms{'bt}}

dform subterms_arity_df : except_mode[src] :: subterms_arity{'bt} =
   `"subterms_arity(" slot{'bt} `")"

let fold_subterms_arity = makeFoldC << subterms_arity{'bt} >> unfold_subterms_arity

interactive subterms_arity_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- subterms_arity{'bt} in nat }

interactive subterms_arity_wf1 {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- subterms_arity{'bt} in int }

(************************************************************************
 * Depth                                                                *
 ************************************************************************)

define unfold_depth: depth{'t} <-->
   fix{ f. lambda{b. (1 +@ list_max{ map{'f; subterms{'b}} })} } 't

dform depth_df : except_mode[src] :: depth{'t} =
   `"depth(" slot{'t} `")"

let fold_depth = makeFoldC << depth{'t} >> unfold_depth

prim depth_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- depth{'bt} in nat } =
   it

interactive depth_wf2 {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- depth{'bt} in int }

interactive depth_subterms {| intro [] |} :
   sequent { <H> >- 'b in BTerm } -->
   sequent { <H> >- 'a in BTerm } -->
   sequent { <H> >- mem{'a; subterms{'b}; BTerm} } -->
   sequent { <H> >- depth {'a} < depth {'b} }

(************************************************************************
 * Bterm elimination rules                                              *
 ************************************************************************)

interactive bterm_elim1 {| elim [ThinOption thinT] |} 'H bind{x.'f['x]} :
   sequent { <H>; b: BTerm; <J['b]>; a: BTerm >- 'f['a] in nat } -->
   sequent { <H>; b: BTerm; <J['b]>; c: BTerm; all a: BTerm. ('f['a] < 'f['c] => 'C['a]) >- 'C['c] } -->
   sequent { <H>; b: BTerm; <J['b]> >- 'C['b] }


interactive bterm_elim2 {| elim [] |} 'H :
   sequent { <H>; b: BTerm; <J['b]>; a: BTerm >- 'C['a] Type} -->
   sequent { <H>; b: BTerm; <J['b]>; c: BTerm; bl: list{BTerm};
      all a: BTerm. (mem{'a; 'bl; BTerm} => 'C['a] & depth{'a} < depth{'c}) >- 'C[make_bterm{'c; 'bl}] } -->
   sequent { <H>; b: BTerm; <J['b]> >- 'C['b] }


interactive bterm_elim3 {| elim [] |} 'H :
   sequent { <H>; b: BTerm; <J['b]>; a: BTerm >- 'C['a] Type} -->
   sequent { <H>; b: BTerm; <J['b]>; c: BTerm; simple_bterm{'c} >- 'C['c] } -->
   sequent { <H>; b: BTerm; <J['b]>; c: BTerm; not{simple_bterm{'c}}; all a: Term. 'C[subst{'c; 'a}] >- 'C['c] } -->
   sequent { <H>; b: BTerm; <J['b]> >- 'C['b] }
