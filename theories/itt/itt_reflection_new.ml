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
extends Itt_synt_bterm
doc docoff


open Dtactic

open Base_reflection
open Basic_tactics
open Itt_nat
open Itt_equal
open Itt_struct
open Itt_squash


(************************************************************************
 * Xlist                                                                *
  ***********************************************************************)

declare xlist_of_list{'l}

prim_rw xlist_list_cons {| reduce |} :
   xlist_of_list{ 'hd :: 'tl } <--> Perv!cons{'hd; xlist_of_list{'tl}}

prim_rw xlist_list_nil {| reduce |} :
   xlist_of_list{ nil } <--> (Perv!nil)

declare list_of_xlist{'l}

prim_rw reduce_xlist_cons :
   list_of_xlist{ (Perv!cons{'hd; 'tl})} <--> ('hd :: list_of_xlist{'tl})

prim_rw reduce_xlist_nil :
   list_of_xlist{ (Perv!nil) } <--> nil

let rec reduce_xlist t =
   if is_xnil_term (one_subterm t) then
      reduce_xlist_nil
   else reduce_xlist_cons thenC addrC [Subterm 2] (termC reduce_xlist)


dform list_of_xlist_df : except_mode[src] :: list_of_xlist{'l} =
   `"list_of_xlist(" slot{'l} `")"

(************************************************************************
 * Var                                                                  *
 ************************************************************************)

prim_rw bterm_var_1 :
  bterm{| x : term >- 'x |} <--> var{0;0}

prim bterm_var_right :
  sequent{ <H> >- bterm{| <K> >- 'x |} ~ var{'l;'r} } -->
  sequent{ <H> >- bterm{| <K>; y:term >- 'x |} ~ var{'l;'r +@ 1} }
  = it

prim bterm_var_left :
  sequent{ <H> >- bterm{| <K> >- 'x |} ~ var{'l;'r} } -->
  sequent{ <H> >- bterm{| y:term; <K> >- 'x |} ~ var{'l +@ 1;'r} }
  = it

(************************************************************************
 * Operator                                                             *
 ************************************************************************)

declare bterm{x.'bt['x]}
prim_rw bterm_reduce: bterm{x.bterm{| <K> >- 't['x] |}} <-->  bterm{| x:term; <K> >- 't['x] |}


prim bterm_op :
  sequent { <H> >- if_quoted_op{'op<||>;"true"} } -->
  sequent { <H> >- 'op<||> in BOperator }
  = it

prim_rw bterm_op_bdepth1 : op_bdepth{ bterm{| >- 'op |}} <--> 0
prim_rw bterm_op_bdepth2 : op_bdepth{ bterm{| x:term; <H> >- 'op |}} <--> op_bdepth{ bterm{| <H> >- 'op |} } +@ 1

prim_rw bterm_arity:
    if_quoted_op{'op<||>;"true"} -->
    arity{'op} <-->  map{lambda{x.op_bdepth{'x}}; list_of_xlist{subterms{'op}} }

prim_rw bterm_same_op:
       is_same_op{'op1;'op2} <--> Base_reflection!if_same_op{'op1;'op2;btrue;bfalse}

prim_rw bterm_inject: inject{bterm{| <K> >- 'op<||> |}; 'n} <--> ind{'n; bterm{| >- 'op<||> |}; k,l.bterm{x.'l}}

(************************************************************************
 * Make_bterm                                                           *
 ************************************************************************)

prim_rw make_bterm_base :
 (if_quoted_op{'op;"true"} ) -->
 ('btl in list{BTerm} ) -->
 (compatible_shapes{'op;'btl}) -->
 make_bterm{'op;'btl} <--> Base_reflection!make_bterm{'op; xlist_of_list{'btl}}

