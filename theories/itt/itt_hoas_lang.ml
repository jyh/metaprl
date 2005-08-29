doc <:doc<
   @module[Itt_hoas_lang]
   The @tt[Itt_hoas_lang] module defines the type of a language over
   a list of operators.

   If <<'ops>> is a list of operators, then <<Lang{'ops}>> is a
   subtype of type <<BTerm>> that contains all terms built
   with operators from the list <<'ops>>.


   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2005, MetaPRL Group

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

doc <:doc< @parents >>
extends Itt_hoas_bterm
extends Itt_image
extends Itt_tunion
doc docoff

open Basic_tactics

doc terms

doc <:doc<
     We define the type <<Lang{'ops}>> as the recursive type.

>>
define unfold_Ldom: dom{'ops; 'BT} <--> nat*nat + depth:nat * op: {op:Operator | find{'ops; 'op; x,y.is_same_op{'x; 'y}} <> length{'ops} } * {subterms:list{'BT} | compatible_shapes{'depth;'op;'subterms} }
(*
define unfold_mk: mk{'x} <--> decide{'x;
                                                  v.spread{'v;left,right. var{'left;'right}};
                                                  t.spread{'t;d,op,st. mk_bterm{'d;'op;'st}}}

define unfold_dest: dest{'bt} <--> dest_bterm{'bt; l,r. inl{('l,'r)}; d,op,ts. inr{('d,('op,'ts))}}
*)
define unfold_LIter: Iter{'ops; 'X} <--> Img{dom{'ops; 'X};x.mk{'x}}

define unfold_LBT: BT{'ops; 'n} <--> ind{'n; void; X.Iter{'ops; 'X}}

define unfold_Lang: Lang{'ops} <--> Union n:nat. BT{'ops; 'n}

(*
define unfold_lang: Lang{'ops} <-->  { t: BTerm | dest_bterm{'t; l,r. "true"; d,op,ts. find{'ops; 'op; x,y.is_same_op{'x; 'y}} <> length{'ops}} }*)
doc docoff

let fold_Lang = makeFoldC << Lang{'ops} >> unfold_Lang

doc rules

interactive_rw lbt_reduce_base {| reduce |}: BT{'ops; 0} <--> void

interactive_rw lbt_reduce_step {| reduce |}: 'n in nat --> BT{'ops; 'n+@1} <--> Iter{'ops; BT{'ops; 'n}}

interactive  lbt_elim_squash  {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'n in nat } -->
   [base] sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   [step] sequent { <H>; <J>; depth: nat; op:{op:Operator | find{'ops; 'op; x,y.is_same_op{'x; 'y}} <> length{'ops} };
             subterms:list{BT{'ops; 'n}}; compatible_shapes{'depth;'op;'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BT{'ops; 'n+@1}; <J> >- squash{'P['t]} }

interactive  lbt_wf_and_bdepth_wf  {| intro[] |}:
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- BT{'ops; 'n} Type & all t: BT{'ops; 'n}. bdepth{'t} in nat }

interactive  lbt_wf {| intro[] |}:
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- BT{'ops; 'n} Type }

interactive lang_wf  {| intro[] |} :
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- Lang{'ops} Type }

interactive  bdepth_wf  {| intro[] |} 'ops :
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent{ <H> >- 't in Lang{'ops} } -->
   sequent{ <H> >- bdepth{'t} in nat }

interactive compatible_shapes_wf {| intro[AutoMustComplete] |} BT{'ops; 'n} :
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 'bdepth in nat } -->
   sequent { <H> >- 'op in {op:Operator | find{'ops; 'op; x,y.is_same_op{'x; 'y}} <> length{'ops} } } -->
   sequent { <H> >- 'btl in list{BT{'ops; 'n}} } -->
   sequent { <H> >- compatible_shapes{'bdepth; 'op; 'btl} Type }

interactive  lbt_subtype_lang  {| intro[] |} :
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'ops; 'n} subtype Lang{'ops} }

interactive ldom_wf1 {| intro[] |}:
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >-  dom{'ops; BT{'ops; 'n}} Type }

interactive  lbt_subtype_bt  {| intro[] |} :
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'ops; 'n} subtype BT{'n} }

interactive lang_subtype  {| intro[] |} :
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- Lang{'ops} subtype BTerm }

interactive  lbt_subtype_bterm  {| intro[] |} :
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'ops; 'n} subtype BTerm }

interactive lbt_monotone  {| intro[] |} :
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'ops; 'n} subtype BT{'ops; 'n+@1} }

interactive ldom_wf {| intro[] |}:
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'T subtype Lang{'ops} } -->
   sequent { <H> >-  dom{'ops; 'T} Type }


interactive lang_intro_var {| intro[] |}:
   sequent { <H> >- 'l in nat } -->
   sequent { <H> >- 'r in nat } -->
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- var{'l;'r} in Lang{'ops} }

interactive lbt_intro_mk_bterm {| intro[] |}:
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- 'depth in nat } -->
   sequent{ <H> >- 'op in {op:Operator | find{'ops; 'op; x,y.is_same_op{'x; 'y}} <> length{'ops} } } -->
   sequent{ <H> >- 'subterms in list{BT{'ops; 'n}} } -->
   sequent{ <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth;'op;'subterms} in BT{'ops; 'n+@1} }

interactive lang_intro_mk_bterm_wf1 {| intro[] |}:
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent{ <H> >- 'depth in nat } -->
   sequent{ <H> >- 'op in {op:Operator | find{'ops; 'op; x,y.is_same_op{'x; 'y}} <> length{'ops} } } -->
   sequent{ <H> >- 'subterms in list{Lang{'ops}} } -->
   sequent{ <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth;'op;'subterms} in Lang{'ops} }

interactive lang_intro_mk_bterm_wf2 {| intro[] |}:
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'depth in nat } -->
   sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- 'subterms in list{Lang{'ops}} } -->
   sequent { <H> >- mem{'op;'ops;Operator}  } -->
   sequent { <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent { <H> >- mk_bterm{'depth;'op;'subterms} in Lang{'ops} }

interactive lang_induction  {| elim[] |} 'H:
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [base] sequent { <H>; x: Lang{'ops}; <J['x]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   [step] sequent { <H>; x: Lang{'ops}; <J['x]>; bdepth: nat; op:Operator; subterms:list{Lang{'ops}};
               compatible_shapes{'bdepth;'op;'subterms}(*; all_list{'subterms; t.'P['t]}*) >- 'P[mk_bterm{'bdepth;'op;'subterms}] } -->
   sequent { <H>; x: Lang{'ops}; <J['x]> >- 'P['x] }

doc docoff

dform lang_df: Lang{'op} =
   tt["Language"] `"[" slot{'op} `"]"
