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
doc docoff
extends Itt_nat

open Dtactic

open Base_reflection
open Basic_tactics
open Itt_nat
open Itt_equal

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




declare bterm

dform bterm_df : except_mode[src] :: bterm =
   `"Bterm"

prim btermEquality {| intro [] |} :
   sequent { <H> >- bterm in univ[i:l] } =
   it

interactive btermType {| intro [] |} :
   sequent { <H> >- bterm Type }

prim bterm_memberEquality {| intro [] |} :
   sequent { <H> >- is_bterm{'x} } -->
   sequent { <H> >- 'x in bterm } =
   it

prim btermFormation {| intro [] |} :
   ('x : sequent { <H> >- bterm }) -->
   sequent { <H> >- bterm } =
   'x

(* ??? use induction for bterm elimination ??? *)




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

prim subterms_wf {| intro [] |} :
   sequent { <H> >- 'bt in bterm } -->
   sequent { <H> >- subterms{'bt} in list{bterm} } =
   it

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of bterm.
 *)
let resource typeinf += (<< bterm >>, infer_univ1)

(* ??? type inference for subterms ??? *)






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

prim makebterm_wf {| intro [] |} :
   sequent { <H> >- 'bt in bterm } -->
   sequent { <H> >- 'btl in list{bterm} } -->
   sequent { <H> >- make_bterm{'bt; 'btl} in bterm } =
   it





define unfold_arity: arity{'bt} <--> length{subterms{'bt}}

dform arity_df : except_mode[src] :: arity{'bt} =
   `"arity(" slot{'bt} `")"

interactive arity_wf {| intro [] |} :
   sequent { <H> >- 'bt in bterm } -->
   sequent { <H> >- arity{'bt} in nat }



(* ??? size ??? *)





define unfold_same_op: same_op{'b1; 'b2} <--> Base_reflection!if_same_op{'b1; 'b2; "true"; "false"}

dform sameop_df : except_mode[src] :: same_op{'b1; 'b2} =
   `"same_op(" slot{'b1} `"; " slot{'b2} `")"

let resource reduce +=
   (<< same_op{ bterm{| <H1> >- 't1 |}; bterm{| <H2> >- 't2 |} } >>, (unfold_same_op thenC Base_reflection.reduce_if_same_op))

prim same_op_wf {| intro [] |} :
   sequent { <H> >- 'b1 in bterm } -->
   sequent { <H> >- 'b2 in bterm } -->
   sequent { <H> >- same_op{'b1; 'b2} Type } =
   it




define unfold_simple_bterm: simple_bterm{'bt} <--> Base_reflection!if_simple_bterm{'bt; "true"; "false"}

dform simple_bterm_df : except_mode[src] :: simple_bterm{'bt} =
   `"simple_bterm(" slot{'bt} `")"

let resource reduce +=
   (<< simple_bterm{ bterm{| <H1> >- 't1 |} } >>, (unfold_simple_bterm thenC Base_reflection.reduce_if_simple_bterm))

prim simple_bterm_wf {| intro [] |} :
   sequent { <H> >- 'bt in bterm } -->
   sequent { <H> >- simple_bterm{'bt} Type } =
   it




define unfold_var_bterm: var_bterm{'bt} <--> Base_reflection!if_var_bterm{'bt; "true"; "false"}

dform var_bterm_df : except_mode[src] :: var_bterm{'bt} =
   `"var_bterm(" slot{'bt} `")"

let resource reduce +=
   (<< var_bterm{ bterm{| <H1> >- 't1 |} } >>, (unfold_var_bterm thenC Base_reflection.reduce_if_var_bterm))

prim var_bterm_wf {| intro [] |} :
   sequent { <H> >- 'bt in bterm } -->
   sequent { <H> >- var_bterm{'bt} Type } =
   it




define unfold_subst: subst{'bt; 't} <--> Base_reflection!subst{'bt; 't}

dform subst_df : except_mode[src] :: subst{'bt; 't} =
   `"subst(" slot{'bt} `"; " slot{'t} `")"

let resource reduce +=
   (<< subst{ bterm{| <H1> >- 't1 |}; bterm{| >- 't2 |} } >>, (unfold_subst thenC Base_reflection.reduce_subst))

prim subst_wf {| intro [] |} :
   sequent { <H> >- 'bt in bterm } -->
   sequent { <H> >- 't in bterm } -->
   sequent { <H> >- simple_bterm{'t} } -->
   sequent { <H> >- subst{'bt; 't} in bterm } =
   it


