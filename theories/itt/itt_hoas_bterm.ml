doc <:doc<
   @module[Itt_hoas_bterm]
   The @tt[Itt_hoas_bterm] module defines the inductive type <<BTerm>>
   and establishes the appropriate induction rules for this type.

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

   Author: Aleksey Kopylov @email{kopylov@cs.caltech.edu}

   @end[license]
>>

doc <:doc< @parents >>
extends Itt_hoas_destterm
extends Itt_hoas_lang
extends Itt_image
extends Itt_tunion

doc docoff

open Basic_tactics
open Itt_hoas_destterm

doc terms

define iform unfold_dom : dom{'BT} <--> dom{Operator; 'BT}
define iform unfold_Iter: Iter{'X} <--> Iter{Operator; 'X}
define iform unfold_BT: BT{'n} <--> BT{Operator; 'n}

define unfold_BTerm: BTerm <--> Lang{Operator}

doc docoff

let fold_BTerm = makeFoldC << BTerm >> unfold_BTerm

doc rules

interactive_rw bt_reduce_base {| reduce |}: BT{0} <--> void

interactive_rw bt_reduce_step {| reduce |}: 'n in nat --> BT{'n+@1} <--> Iter{BT{'n}}

interactive  bt_elim_squash  {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'n in nat } -->
   [base] sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   [step] sequent { <H>; <J>; depth: nat; op:Operator; subterms:list{BT{'n}};
               compatible_shapes{'depth;'op;'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BT{'n+@1}; <J> >- squash{'P['t]} }

interactive  bt_wf_and_bdepth_wf  {| intro[] |}:
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- BT{'n} Type & all t: BT{'n}. bdepth{'t} in nat }

interactive  bt_wf {| intro[] |}:
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- BT{'n} Type }

interactive  bterm_wf {| intro[] |}:
   sequent{ <H> >- BTerm Type }

interactive  bdepth_wf  {| intro[] |}:
   sequent{ <H> >- 't in BTerm } -->
   sequent{ <H> >- bdepth{'t} in nat }

interactive compatible_shapes_wf {| intro[] |}:
   sequent{ <H> >- 'bdepth in nat } -->
   sequent{ <H> >- 'op in Operator } -->
   sequent{ <H> >- 'btl in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'bdepth; 'op; 'btl} Type }

interactive dom_wf {| intro[] |}:
   sequent{ <H> >- 'T subtype BTerm } -->
   sequent{ <H> >-  dom{'T} Type }

interactive bt_subtype_bterm  {| intro[] |} :
   sequent{ <H> >- 'n in nat} -->
   sequent{ <H> >- BT{'n} subtype BTerm }

interactive bt_monotone  {| intro[] |} :
   sequent{ <H> >- 'n in nat} -->
   sequent{ <H> >- BT{'n} subtype BT{'n+@1} }


interactive var_wf {| intro[] |}:
   sequent{ <H> >- 'l in nat } -->
   sequent{ <H> >- 'r in nat } -->
   sequent{ <H> >- var{'l;'r} in BTerm }

interactive mk_bterm_bt_wf {| intro[] |}:
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- 'depth in nat } -->
   sequent{ <H> >- 'op in Operator } -->
   sequent{ <H> >- 'subterms in list{BT{'n}} } -->
   sequent{ <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth;'op;'subterms} in BT{'n+@1} }

interactive mk_bterm_wf {| intro[] |}:
   sequent{ <H> >- 'depth in nat } -->
   sequent{ <H> >- 'op in Operator } -->
   sequent{ <H> >- 'subterms in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth;'op;'subterms} in BTerm }

interactive  bt_elim_squash2  {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'n in nat } -->
   [base] sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   [step] sequent { <H>; 'n>0; <J>; depth: nat; op:Operator; subterms:list{BT{'n-@1}};
               compatible_shapes{'depth;'op;'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BT{'n}; <J> >- squash{'P['t]} }

interactive  bterm_elim_squash {| elim [] |} 'H :
   sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   sequent { <H>; <J>; depth: nat; op:Operator; subterms:list{BTerm};
               compatible_shapes{'depth;'op;'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BTerm; <J> >- squash{'P['t]} }

interactive_rw bind_eta {| reduce |} :
   'bt in BTerm -->
   bdepth{'bt} > 0 -->
   bind{x. subst{'bt; 'x}} <--> 'bt

interactive_rw bind_vec_eta {| reduce |} :
   'n in nat -->
   'bt in BTerm -->
    bdepth{'bt} >= 'n -->
    bind{'n; gamma. substl{'bt; 'gamma}} <--> 'bt

interactive_rw subterms_lemma {| reduce |} :
   'n in nat -->
   'subterms in list{BTerm} -->
   all i:Index{'subterms}. bdepth{nth{'subterms;'i}} >=  'n -->
   map{bt. bind{'n; v. substl{'bt; 'v}};'subterms} <--> 'subterms

interactive_rw dest_bterm_mk_bterm2 {| reduce |} :
   'n in nat -->
   'op in Operator -->
   'subterms in list{BTerm} -->
   compatible_shapes{'n;'op;'subterms} -->
   dest_bterm{mk_bterm{'n; 'op; 'subterms}; l,r.'var_case['l; 'r]; bdepth,op,subterms. 'op_case['bdepth; 'op; 'subterms] }
   <-->
   'op_case['n; 'op; 'subterms]

interactive_rw mk_dest_reduce {| reduce |}:
   't in BTerm  -->
   mk{dest{'t}} <--> 't

interactive dest_bterm_wf {| intro[] |}:
   sequent{ <H> >- 'bt in BTerm } -->
   sequent{ <H>; l:nat; r:nat >- 'var_case['l;'r] in 'T } -->
   sequent{ <H>; bdepth: nat; op:Operator; subterms:list{BTerm};
                 compatible_shapes{'bdepth;'op;'subterms}
                 >- 'op_case['bdepth; 'op; 'subterms] in 'T } -->
   sequent{ <H> >- dest_bterm{'bt; l,r.'var_case['l; 'r]; bdepth,op,subterms. 'op_case['bdepth; 'op; 'subterms]} in 'T }

interactive dest_wf {| intro[] |}:
   sequent{ <H> >- 't in BTerm } -->
   sequent{ <H> >-  dest{'t} in dom{BTerm} }

interactive bterm_elim  {| elim [] |} 'H :
   sequent { <H>; <J>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; <J>; bdepth: nat; op:Operator; subterms:list{BTerm};
               compatible_shapes{'bdepth;'op;'subterms} >- 'P[mk_bterm{'bdepth;'op;'subterms}] } -->
   sequent { <H>; t: BTerm; <J> >- 'P['t] }

(* *** *)
interactive dom_elim  {| elim [] |} 'H :
   sequent { <H>; t: dom{'T}; u: nat*nat; <J[inl{'u}]> >- 'P[inl{'u}] } -->
   sequent { <H>; t: dom{'T}; v: depth:nat * op:Operator * {subterms:list{'T} | compatible_shapes{'depth;'op;'subterms}}; <J[inr{'v}]>
               >- 'P[inr{'v}] } -->
   sequent { <H>; t: dom{'T}; <J['t]> >- 'P['t] }

interactive_rw dest_mk_reduce 'n :
   'n in nat -->
   't in dom{BT{'n}}  -->
   dest{mk{'t}} <--> 't

interactive  bt_elim_squash1  {| elim [] |} 'H :
   [wf] sequent { <H> >- 'n in nat } -->
   [base] sequent { <H>; t: BT{'n+@1}; <J['t]>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   [step] sequent { <H>; t: BT{'n+@1}; <J['t]>; depth: nat; op:Operator; subterms:list{BT{'n}};
               compatible_shapes{'depth;'op;'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BT{'n+@1}; <J['t]> >- squash{'P['t]} }

interactive  bt_elim1  {| elim [] |} 'H :
   [wf] sequent { <H> >- 'n in nat } -->
   [step] sequent { <H>; t: BT{'n+@1}; <J['t]>; x: dom{BT{'n}} >- 'P[mk{'x}] } -->
   sequent { <H>; t: BT{'n+@1}; <J['t]> >- 'P['t] }

interactive  bterm_elim_squash1 {| elim [] |} 'H :
   sequent { <H>; t: BTerm; <J['t]>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   sequent { <H>; t: BTerm; <J['t]>; depth: nat; op:Operator; subterms:list{BTerm};
               compatible_shapes{'depth;'op;'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BTerm; <J['t]> >- squash{'P['t]} }

interactive bterm_elim2  {| elim [] |} 'H :
   sequent { <H>; t: BTerm; <J['t]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; t: BTerm; <J['t]>; bdepth: nat; op:Operator; subterms:list{BTerm};
               compatible_shapes{'bdepth;'op;'subterms} >- 'P[mk_bterm{'bdepth;'op;'subterms}] } -->
   sequent { <H>; t: BTerm; <J['t]> >- 'P['t] }

interactive is_var_wf {| intro[] |}:
   sequent{ <H> >- 't in BTerm } -->
   sequent{ <H> >-  is_var{'t} in bool }

interactive subterms_depth {| intro[] |} 'op :
   sequent{ <H> >- 'bdepth in nat } -->
   sequent{ <H> >- 'op in Operator } -->
   sequent{ <H> >- 'btl in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'bdepth; 'op; 'btl} } -->
   sequent{ <H> >- all i:Index{'btl}. bdepth{nth{'btl;'i}} >= 'bdepth }

interactive subterms_wf1 {| intro[] |}:
   sequent{ <H> >- 't in BTerm } -->
   sequent{ <H> >- not{"assert"{is_var{'t}}} } -->
   sequent{ <H> >- subterms{'t} in list{BTerm} }

doc docoff

dform compatible_shapes_df: compatible_shapes{'bdepth;'op;'btl} =
   tt["compatible_shapes"] `"(" slot{'bdepth} `";" slot{'op} `";" slot{'btl} `")"

dform bterm_df: BTerm = keyword["BTerm"]
