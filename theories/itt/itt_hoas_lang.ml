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
extends Itt_list2
doc docoff

open Basic_tactics

doc terms

doc <:doc<
     We define the type <<Lang{'ops}>> as the recursive type.

>>
define iform unfold_SubOp : SubOp{'ops} <--> listmem_set{'ops; Operator}

define unfold_Ldom: dom{'ops; 'BT} <--> nat*nat + depth:nat * op: SubOp{'ops} * {subterms:list{'BT} | compatible_shapes{'depth;'op;'subterms} }
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
   [step] sequent { <H>; <J>; depth: nat; op:SubOp{'ops}; subterms:list{BT{'ops; 'n}};
             compatible_shapes{'depth;'op;'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
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
   sequent { <H> >- 'op in SubOp{'ops} } -->
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
   sequent{ <H> >- 'op in SubOp{'ops} } -->
   sequent{ <H> >- 'subterms in list{BT{'ops; 'n}} } -->
   sequent{ <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth;'op;'subterms} in BT{'ops; 'n+@1} }

interactive lang_intro_mk_bterm_wf1 {| intro[] |}:
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent{ <H> >- 'depth in nat } -->
   sequent{ <H> >- 'op in SubOp{'ops} } -->
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


interactive  lbt_elim_squash1  {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'n in nat } -->
   [wf] sequent { <H>; <J> >- 'ops in list{Operator} } -->
   [base] sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   [step] sequent { <H>; 'n>0; <J>; depth: nat; op: SubOp{'ops}; subs: list{BT{'ops; 'n-@1}};
               compatible_shapes{'depth;'op;'subs} >- squash{'P[mk_bterm{'depth;'op;'subs}]} } -->
   sequent { <H>; t: BT{'ops; 'n}; <J> >- squash{'P['t]} }

interactive  lang_elim_squash {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'ops in list{Operator} } -->
   sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   sequent { <H>; <J>; depth: nat; op: SubOp{'ops}; subs: list{Lang{'ops}};
                compatible_shapes{'depth;'op;'subs} >- squash{'P[mk_bterm{'depth;'op;'subs}]} } -->
   sequent { <H>; t: Lang{'ops}; <J> >- squash{'P['t]} }

interactive_rw mk_dest_reduce 'ops :
   'ops in list{Operator} -->
   't in Lang{'ops}  -->
   mk{dest{'t}} <--> 't

interactive dest_bterm_wf {| intro[intro_typeinf <<'bt>>] |} Lang{'ops} :
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent{ <H> >- 'bt in Lang{'ops} } -->
   sequent{ <H>; l:nat; r:nat >- 'var_case['l;'r] in 'T } -->
   sequent{ <H>; bdepth: nat; op: SubOp{'ops}; subterms: list{Lang{'ops}};
                 compatible_shapes{'bdepth;'op;'subterms} >- 'op_case['bdepth; 'op; 'subterms] in 'T } -->
   sequent{ <H> >- dest_bterm{'bt; l,r.'var_case['l; 'r]; bdepth,op,subterms. 'op_case['bdepth; 'op; 'subterms]} in 'T }

interactive dest_wf {| intro[] |}:
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent{ <H> >- 't in Lang{'ops} } -->
   sequent{ <H> >-  dest{'t} in dom{'ops; Lang{'ops}} }

interactive lang_elim  {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'ops in list{Operator} } -->
   sequent { <H>; <J>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; <J>; bdepth: nat; op: SubOp{'ops}; subs: list{Lang{'ops}};
               compatible_shapes{'bdepth;'op;'subs} >- 'P[mk_bterm{'bdepth;'op;'subs}] } -->
   sequent { <H>; t: Lang{'ops}; <J> >- 'P['t] }

interactive  lbt_elim_squash2  {| elim [] |} 'H :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [base] sequent { <H>; t: BT{'ops; 'n+@1}; <J['t]>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   [step] sequent { <H>; t: BT{'ops; 'n+@1}; <J['t]>; depth: nat; op: SubOp{'ops}; subs: list{BT{'ops; 'n}};
                compatible_shapes{'depth;'op;'subs} >- squash{'P[mk_bterm{'depth;'op;'subs}]} } -->
   sequent { <H>; t: BT{'ops; 'n+@1}; <J['t]> >- squash{'P['t]} }

interactive ldom_elim  {| elim [] |} 'H :
   sequent { <H>; t: dom{'ops; 'T}; u: nat*nat; <J[inl{'u}]> >- 'P[inl{'u}] } -->
   sequent { <H>; t: dom{'ops;'T}; v: depth:nat * op:SubOp{'ops} * {subterms:list{'T} | compatible_shapes{'depth;'op;'subterms}}; <J[inr{'v}]>
               >- 'P[inr{'v}] } -->
   sequent { <H>; t: dom{'ops;'T}; <J['t]> >- 'P['t] }

interactive_rw dest_mk_reduce BT{'ops; 'n} :
   'ops in list{Operator} -->
   'n in nat -->
   't in dom{'ops; BT{'ops; 'n}}  -->
   dest{mk{'t}} <--> 't

interactive  lbt_elim1  {| elim [] |} 'H :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [step] sequent { <H>; t: BT{'ops; 'n+@1}; <J['t]>; x: dom{'ops; BT{'ops; 'n}} >- 'P[mk{'x}] } -->
   sequent { <H>; t: BT{'ops; 'n+@1}; <J['t]> >- 'P['t] }

interactive  lang_elim_squash1 {| elim [] |} 'H :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H>; t: Lang{'ops}; <J['t]>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   sequent { <H>; t: Lang{'ops}; <J['t]>; depth: nat; op: SubOp{'ops}; subs: list{Lang{'ops}};
               compatible_shapes{'depth;'op;'subs} >- squash{'P[mk_bterm{'depth;'op;'subs}]} } -->
   sequent { <H>; t: Lang{'ops}; <J['t]> >- squash{'P['t]} }

interactive lang_induction  {| elim [] |} 'H :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [base] sequent { <H>; t: Lang{'ops}; <J['t]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   [step] sequent { <H>; t: Lang{'ops}; <J['t]>; bdepth: nat; op: SubOp{'ops}; subs: list{Lang{'ops}};
               compatible_shapes{'bdepth;'op;'subs} >- 'P[mk_bterm{'bdepth;'op;'subs}] } -->
   sequent { <H>; t: Lang{'ops}; <J['t]> >- 'P['t] }

interactive lang_induction2  {| elim [] |} 'H :
   [wf] sequent { <H> >- 'h in Operator } -->
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H>; t: Lang{'h::'ops}; <J['t]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; t: Lang{'h::'ops}; <J['t]>; bdepth: nat; subs: list{Lang{'h::'ops}};
               compatible_shapes{'bdepth;'h;'subs} >- 'P[mk_bterm{'bdepth;'h;'subs}] } -->
   sequent { <H>; t: Lang{'h::'ops}; <J['t]>; bdepth: nat; op: SubOp{'ops}; subs: list{Lang{'h::'ops}};
               compatible_shapes{'bdepth;'op;'subs} >- 'P[mk_bterm{'bdepth;'op;'subs}] } -->
   sequent { <H>; t: Lang{'h::'ops}; <J['t]> >- 'P['t] }

doc docoff

dform lang_df: Lang{'op} =
   tt["Language"] `"[" slot{'op} `"]"
