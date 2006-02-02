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

   Copyright (C) 2005-2006, MetaPRL Group

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
extends Itt_image
extends Itt_tunion
extends Itt_subset
doc docoff

open Basic_tactics
open Itt_sqsimple
open Itt_hoas_destterm

doc terms

doc <:doc<
    We define the type <<BTerm>> as a recursive type.
    The << compatible_shapes{'depth; 'shape; 'subterms} >> predicate defines when
    a list of subterms << 'subterms >> is compatible with a specific operator.

>>
define unfold_compatible_shapes: compatible_shapes{'depth; 'shape; 'btl} <-->
   all2{'shape; 'btl; x, y. ('depth +@ 'x) = bdepth{'y} in int}

define unfold_dom: dom{'BT} <--> nat*nat + depth:nat * op: Operator * {subterms:list{'BT} | compatible_shapes{'depth;shape{'op};'subterms} }

define unfold_mk: mk{'x} <--> decide{'x;
                                      v.spread{'v;left,right. var{'left;'right}};
                                      t.spread{'t;d,op,st. mk_bterm{'d;'op;'st}}}

define unfold_dest: dest{'bt} <--> dest_bterm{'bt; l,r. inl{('l,'r)}; d,op,ts. inr{('d,('op,'ts))}}

define unfold_Iter: Iter{'X} <--> Img{dom{'X};x.mk{'x}}

define unfold_BT: BT{'n} <--> ind{'n; void; X.Iter{'X}}

define unfold_BTerm: BTerm <--> Union n:nat. BT{'n}

define unfold_BTerm2 : BTerm{'i} <--> { e: BTerm | bdepth{'e} = 'i in nat }

define (*privite *) unfold_ndepth:
   ndepth{'t} <-->
    fix{ndepth. lambda{t.
      dest_bterm{'t; l,r.1; bdepth,op,subterms. list_max{map{x.'ndepth 'x;'subterms}}+@ 1 }
    }} 't

doc docoff

let fold_compatible_shapes = makeFoldC << compatible_shapes{'depth; 'shape; 'btl} >> unfold_compatible_shapes
let fold_dom = makeFoldC << dom{'BT} >> unfold_dom
let fold_mk = makeFoldC << mk{'x} >> unfold_mk
let fold_dest = makeFoldC << dest{'bt} >> unfold_dest
let fold_Iter = makeFoldC << Iter{'X} >> unfold_Iter
let fold_BT = makeFoldC << BT{'n} >> unfold_BT
let fold_BTerm = makeFoldC << BTerm >> unfold_BTerm
let fold_BTerm2 = makeFoldC << BTerm{'i} >> unfold_BTerm2
let fold_ndepth = makeFoldC << ndepth{'t} >> unfold_ndepth

interactive_rw compatible_shapes_nil_nil {| reduce |} :
   compatible_shapes{'depth; nil; nil}
   <-->
   "true"

interactive_rw compatible_shapes_nil_cons {| reduce |} :
   compatible_shapes{'depth; nil; 'h2 :: 't2}
   <-->
   "false"

interactive_rw compatible_shapes_cons_nil {| reduce |} :
   compatible_shapes{'depth; 'h1 :: 't1; nil}
   <-->
   "false"

interactive_rw compatible_shapes_cons_cons {| reduce |} :
   compatible_shapes{'depth; 'h1 :: 't1; 'h2 :: 't2}
   <-->
   (('depth +@ 'h1) = bdepth{'h2} in int) & compatible_shapes{'depth; 't1; 't2}

interactive_rw bt_reduce_base {| reduce |}: BT{0} <--> void

interactive_rw bt_reduce_step {| reduce |}: 'n in nat --> BT{'n +@ 1} <--> Iter{BT{'n}}

doc rules

interactive bt_elim_squash  {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'n in nat } -->
   [base] sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   [step] sequent { <H>; <J>; depth: nat; op:Operator; subterms:list{BT{'n}};
               compatible_shapes{'depth; shape{'op}; 'subterms}
               >- squash{'P[mk_bterm{'depth; 'op; 'subterms}]} } -->
   sequent { <H>; t: BT{'n+@1}; <J> >- squash{'P['t]} }

interactive bt_elim_squash0  {| nth_hyp |} 'H :
   sequent { <H>; t: BT{0}; <J> >- 'P['t] }

interactive bt_wf_and_bdepth_univ  {| intro[] |}:
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- BT{'n} in univ[l:l] & all t: BT{'n}. bdepth{'t} in nat }

interactive bt_wf_and_bdepth_wf  {| intro [] |}:
   [wf] sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- BT{'n} Type & all t: BT{'n}. bdepth{'t} in nat }

interactive bt_univ {| intro[] |}:
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- BT{'n} in univ[l:l] }

interactive bt_wf {| intro [] |}:
   [wf] sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- BT{'n} Type }

interactive bterm_univ  {| intro[] |} :
   sequent { <H> >- BTerm in univ[l:l] }

interactive  bterm_wf {| intro [] |}:
   sequent{ <H> >- BTerm Type }

interactive  bdepth_wf  {| intro [] |}:
   [wf] sequent{ <H> >- 't in BTerm } -->
   sequent{ <H> >- bdepth{'t} in nat }

interactive  bdepth_wf_int  {| intro [] |}:
   [wf] sequent{ <H> >- 't in BTerm } -->
   sequent{ <H> >- bdepth{'t} in int }

interactive bterm2_wf {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- BTerm{'n} Type }

interactive compatible_shapes_univ {| intro [] |} :
   [wf] sequent { <H> >- 'bdepth in nat } -->
   [wf] sequent { <H> >- 'shape in list{int} } -->
   [wf] sequent { <H> >- 'btl in list{BTerm} } -->
   sequent { <H> >- compatible_shapes{'bdepth; 'shape; 'btl} in univ[l:l] }

interactive compatible_shapes_wf {| intro [] |} :
   [wf] sequent{ <H> >- 'bdepth in nat } -->
   [wf] sequent{ <H> >- 'shape in list{int} } -->
   [wf] sequent{ <H> >- 'btl in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'bdepth; 'shape; 'btl} Type }

interactive bt_subtype_bterm  {| intro[] |} :
   [wf] sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'n} subtype BTerm }

interactive dom_wf1 {| intro[] |}:
   [wf] sequent { <H> >- 'n in nat} -->
   sequent { <H> >-  dom{BT{'n}} Type }

interactive compatible_shapes_sqstable (*{| squash |}*) :
   [wf] sequent { <H> >- 'bdepth in int } -->
   [wf] sequent{ <H> >- 'shape in list{int} } -->
   [wf] sequent{ <H> >- 'btl in list{BTerm} } -->
   sequent{ <H> >- squash{compatible_shapes{'bdepth; 'shape; 'btl}}  } -->
   sequent{ <H> >- compatible_shapes{'bdepth; 'shape; 'btl} }

interactive dom_wf {| intro [] |}:
   sequent{ <H> >- 'T subtype BTerm } -->
   sequent{ <H> >-  dom{'T} Type }

interactive dom_monotone {| intro[] |}:
   sequent{ <H> >- 'T subtype 'S } -->
   sequent { <H> >- 'S subtype BTerm } -->
   sequent{ <H> >-  dom{'T} subtype dom{'S} }

interactive dom_monotone_set {| intro[] |}:
   sequent{ <H> >- 'T subset 'S } -->
   sequent { <H> >- 'S subtype BTerm } -->
   sequent{ <H> >-  dom{'T} subset dom{'S} }

interactive iter_monotone {| intro[] |}:
   sequent{ <H> >- 'T subtype 'S } -->
   sequent { <H> >- 'S subtype BTerm } -->
   sequent{ <H> >-  Iter{'T} subtype Iter{'S} }

interactive bt_monotone  {| intro [] |} :
   [wf] sequent{ <H> >- 'n in nat} -->
   sequent{ <H> >- BT{'n} subtype BT{'n+@1} }

interactive var_wf0 {| intro[] |}:
   sequent { <H> >- 'X subtype BTerm } -->
   [wf] sequent { <H> >- 'l in nat } -->
   [wf] sequent { <H> >- 'r in nat } -->
   sequent { <H> >- var{'l;'r} in Iter{'X} }

interactive var_wf {| intro [] |}:
   [wf] sequent{ <H> >- 'l in nat } -->
   [wf] sequent{ <H> >- 'r in nat } -->
   sequent{ <H> >- var{'l;'r} in BTerm }

interactive mk_bterm_bt_wf {| intro [] |} :
   [wf] sequent{ <H> >- 'n in nat } -->
   [wf] sequent{ <H> >- 'depth in nat } -->
   [wf] sequent{ <H> >- 'op in Operator } -->
   [wf] sequent{ <H> >- 'subterms in list{BT{'n}} } -->
   sequent{ <H> >- compatible_shapes{'depth; shape{'op}; 'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth; 'op; 'subterms} in BT{'n+@1} }

interactive mk_bterm_wf {| intro [] |} :
   [wf] sequent{ <H> >- 'depth in nat } -->
   [wf] sequent{ <H> >- 'op in Operator } -->
   [wf] sequent{ <H> >- 'subterms in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'depth; shape{'op}; 'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth; 'op; 'subterms} in BTerm }

interactive mk_bterm_wf2 {| intro [] |} :
   [wf] sequent{ <H> >- 'd1 = 'd2 in nat } -->
   [wf] sequent{ <H> >- 'op in Operator } -->
   [wf] sequent{ <H> >- 'subterms in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'d1; shape{'op}; 'subterms} } -->
   sequent{ <H> >- mk_bterm{'d1; 'op; 'subterms} in BTerm{'d2} }

interactive mk_term_wf {| intro [] |} :
   [wf] sequent{ <H> >- 'op in Operator } -->
   [wf] sequent{ <H> >- 'subterms in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{0; shape{'op}; 'subterms} } -->
   sequent{ <H> >- mk_term{'op; 'subterms} in BTerm }

interactive mk_term_wf2 {| intro [] |} :
   [wf] sequent { <H> >- 'd = 0 in nat } -->
   [wf] sequent { <H> >- 'op in Operator } -->
   [wf] sequent { <H> >- 'subterms in list{BTerm} } -->
   sequent { <H> >- compatible_shapes{0; shape{'op}; 'subterms} } -->
   sequent { <H> >- mk_term{'op; 'subterms} in BTerm{'d} }

interactive bt_elim_squash2  {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'n in nat } -->
   [base] sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   [step] sequent { <H>; 'n>0; <J>; depth: nat; op:Operator; subterms:list{BT{'n-@1}};
               compatible_shapes{'depth;shape{'op};'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BT{'n}; <J> >- squash{'P['t]} }

interactive bterm_elim_squash {| elim [] |} 'H :
   sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   sequent { <H>; <J>; depth: nat; op:Operator; subterms:list{BTerm};
               compatible_shapes{'depth;shape{'op};'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BTerm; <J> >- squash{'P['t]} }

interactive bterm_induction_squash1 'H :
   sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   sequent { <H>; <J>; n: nat; depth: nat; op:Operator; subterms:list{BT{'n}};
               compatible_shapes{'depth;shape{'op};'subterms};
               all_list{'subterms;t.squash{'P['t]}}
               >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
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
   all i:Index{'subterms}. bdepth{nth{'subterms;'i}} >= 'n -->
   map{bt. bind{'n; v. substl{'bt; 'v}};'subterms} <--> 'subterms

interactive subterms_depth {| intro [] |} 'shape :
   [wf] sequent{ <H> >- 'bdepth in nat } -->
   [wf] sequent{ <H> >- 'shape in list{nat} } -->
   [wf] sequent{ <H> >- 'btl in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'bdepth; 'shape; 'btl} } -->
   sequent{ <H> >- all i:Index{'btl}. bdepth{nth{'btl;'i}} >= 'bdepth }

interactive subterms_depth2 {| intro [] |} 'shape :
   [wf] sequent{ <H> >- 'bdepth in nat } -->
   [wf] sequent{ <H> >- 'shape in list{nat} } -->
   [wf] sequent{ <H> >- 'btl in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'bdepth; 'shape; 'btl} } -->
   sequent{ <H> >- all i:Index{'btl}. 'bdepth <= bdepth{nth{'btl;'i}} }

interactive subterms_depth3 {| intro [] |} 'shape :
   [wf] sequent{ <H> >- 'bdepth in nat } -->
   [wf] sequent{ <H> >- 'shape in list{nat} } -->
   [wf] sequent{ <H> >- 'btl in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'bdepth; 'shape; 'btl} } -->
   sequent{ <H> >- all_list{'btl; x. bdepth{'x} >= 'bdepth} }

interactive_rw dest_bterm_mk_bterm2 {| reduce |} :
   'n in nat -->
   'op in Operator -->
   'subterms in list{BTerm} -->
   compatible_shapes{'n;shape{'op};'subterms} -->
   dest_bterm{ mk_bterm{'n; 'op; 'subterms};
              l,r.'var_case['l; 'r];
              bdepth,op,subterms. 'op_case['bdepth; 'op; 'subterms] }
   <-->
   'op_case['n; 'op; 'subterms]

interactive_rw dest_bterm_mk_term {| reduce |} :
   'op in Operator -->
   'subterms in list -->
   dest_bterm{mk_term{'op; 'subterms}; l, r.'var_case['l; 'r]; bdepth, op, subterms. 'op_case['bdepth; 'op; 'subterms] }
   <-->
   'op_case[0; 'op; 'subterms]

interactive_rw mk_dest_reduce {| reduce |}:
   't in BTerm  -->
   mk{dest{'t}} <--> 't

interactive_rw reduce_ndepth1 {| reduce |}:
   ('l in nat) -->
   ('r in nat) -->
   ndepth{var{'l;'r}} <--> 1

interactive_rw reduce_ndepth2 {| reduce |}:
   'op in Operator -->
   'bdepth in nat -->
   'subs in list{BTerm} -->
   compatible_shapes{'bdepth;shape{'op};'subs} -->
   ndepth{mk_bterm{'bdepth;'op;'subs}} <--> list_max{map{x.ndepth{'x};'subs}}+@ 1

interactive iter_monotone_set {| intro[] |}:
   sequent{ <H> >- 'T subset 'S } -->
   sequent { <H> >- 'S subtype BTerm } -->
   sequent{ <H> >-  Iter{'T} subset Iter{'S} }

interactive bt_monotone_set  {| intro[] |} :
   [wf] sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'n} subset BT{'n+@1} }

interactive bt_monotone_set2  {| intro[] |} :
   [wf] sequent { <H> >- 'k in nat} -->
   [wf] sequent { <H> >- 'n in nat} -->
   sequent { <H> >- 'k <= 'n} -->
   sequent { <H> >- BT{'k} subset BT{'n} }

interactive ndepth_wf {| intro[] |}:
   [wf] sequent{ <H> >- 't in BTerm } -->
   sequent { <H> >-  ndepth{'t} in nat }

interactive ndepth_correct {| intro[] |} :
   [wf] sequent{ <H> >- 't in BTerm } -->
   sequent { <H> >-  't in BT{ndepth{'t}} }

interactive bt_subset_bterm  {| intro [] |} :
   [wf] sequent{ <H> >- 'n in nat} -->
   sequent{ <H> >- BT{'n} subset BTerm }

interactive dest_bterm_wf {| intro [] |}:
   [wf] sequent{ <H> >- 'bt in BTerm } -->
   [wf] sequent{ <H>; l:nat; r:nat >- 'var_case['l;'r] in 'T } -->
   [wf] sequent{ <H>; bdepth: nat; op:Operator; subterms:list{BTerm};
                 compatible_shapes{'bdepth;shape{'op};'subterms}
                 >- 'op_case['bdepth; 'op; 'subterms] in 'T } -->
   sequent{ <H> >- dest_bterm{'bt; l,r.'var_case['l; 'r]; bdepth,op,subterms. 'op_case['bdepth; 'op; 'subterms]} in 'T }

interactive dest_wf {| intro [] |}:
   [wf] sequent{ <H> >- 't in BTerm } -->
   sequent{ <H> >-  dest{'t} in dom{BTerm} }

interactive bterm_elim  {| elim [] |} 'H :
   sequent { <H>; <J>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; <J>; bdepth: nat; op:Operator; subterms:list{BTerm};
               compatible_shapes{'bdepth;shape{'op};'subterms} >- 'P[mk_bterm{'bdepth;'op;'subterms}] } -->
   sequent { <H>; t: BTerm; <J> >- 'P['t] }

(* *** *)
interactive dom_elim  {| elim [] |} 'H :
   sequent { <H>; t: dom{'T}; u: nat*nat; <J[inl{'u}]> >- 'P[inl{'u}] } -->
   sequent { <H>; t: dom{'T}; v: depth:nat * op:Operator * {subterms:list{'T} | compatible_shapes{'depth;shape{'op};'subterms}}; <J[inr{'v}]>
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
               compatible_shapes{'depth;shape{'op};'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BT{'n+@1}; <J['t]> >- squash{'P['t]} }

interactive  bt_elim1  {| elim [] |} 'H :
   [wf] sequent { <H> >- 'n in nat } -->
   [step] sequent { <H>; t: BT{'n+@1}; <J['t]>; x: dom{BT{'n}} >- 'P[mk{'x}] } -->
   sequent { <H>; t: BT{'n+@1}; <J['t]> >- 'P['t] }

interactive  bterm_elim_squash1 {| elim [] |} 'H :
   sequent { <H>; t: BTerm; <J['t]>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   sequent { <H>; t: BTerm; <J['t]>; depth: nat; op:Operator; subterms:list{BTerm};
               compatible_shapes{'depth;shape{'op};'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BTerm; <J['t]> >- squash{'P['t]} }

interactive bterm_elim2  {| elim [] |} 'H :
   sequent { <H>; t: BTerm; <J['t]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; t: BTerm; <J['t]>; bdepth: nat; op:Operator; subterms:list{BTerm};
               compatible_shapes{'bdepth;shape{'op};'subterms} >- 'P[mk_bterm{'bdepth;'op;'subterms}] } -->
   sequent { <H>; t: BTerm; <J['t]> >- 'P['t] }

doc <:doc<
   The following is the actual induction principle (the previous
   rules are just elimination rules).
>>
interactive bterm_induction {| elim [] |} 'H :
   [base] sequent { <H>; t: BTerm; <J['t]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   [step] sequent { <H>; t: BTerm; <J['t]>; bdepth: nat; op: Operator;
               subterms: list{BTerm};
               compatible_shapes{'bdepth; shape{'op}; 'subterms};
               all_list{'subterms; t. 'P['t]}
               >- 'P[mk_bterm{'bdepth;'op;'subterms}] } -->
   sequent { <H>; t: BTerm; <J['t]> >- 'P['t] }

interactive is_var_wf {| intro [] |}:
   [wf] sequent{ <H> >- 't in BTerm } -->
   sequent{ <H> >-  is_var{'t} in bool }

interactive subterms_wf1 {| intro [] |}:
   [wf] sequent{ <H> >- 't in BTerm } -->
   sequent{ <H> >- not{"assert"{is_var{'t}}} } -->
   sequent{ <H> >- subterms{'t} in list{BTerm} }

doc docoff

dform compatible_shapes_df: compatible_shapes{'bdepth;'op;'btl} =
   tt["compatible_shapes"] `"(" slot{'bdepth} `";" slot{'op} `";" slot{'btl} `")"

dform bterm_df : BTerm = keyword["BTerm"]

(************************************************************************
 * Fold up Aleksey's dummy term.
 *)
define unfold_dummy :
   dummy
   <-->
   mk_term{it; nil}

let fold_dummy = makeFoldC << dummy >> unfold_dummy

(************************************************************************
 * Conversions.
 *)
interactive_rw reduce_bdepth_bind {| reduce |} :
   'e in BTerm -->
   bdepth{'e} > 0 -->
   bdepth{subst{'e; dummy}}
   <-->
   bdepth{'e} -@ 1

(************************************************************************
 * Eta-expansion.
 *)
doc <:doc<
   When proving facts about specific terms and languages, we often need
   eta-expansion because the representation of specific terms with binders
   uses an explicit bind term.
>>
let bind_opname = opname_of_term << bind{x. 'e} >>
let mk_bind_term = mk_dep1_term bind_opname
let dest_bind_term = dest_dep1_term bind_opname

let subst_opname = opname_of_term << subst{'e1; 'e2} >>
let mk_subst_term = mk_dep0_dep0_term subst_opname
let dest_subst_term = dest_dep0_dep0_term subst_opname

let var_x = Lm_symbol.add "x"
let eta_expand e t =
   if alpha_equal t e then
      (* The result term *)
      let x = maybe_new_var_set var_x (free_vars_set e) in
      let bind = mk_bind_term x (mk_subst_term e (mk_var_term x)) in
         foldC bind bind_eta
   else
      failC

let etaExpandC e =
   termC (eta_expand e)

(************************************************************************
 * Squiggle equality.
 *)
doc docoff

interactive var_squiggle  :
   [wf] sequent { <H> >- 'x in Var } -->
   [wf] sequent { <H> >- 'y in Var } -->
   [aux] sequent { <H> >- 'x = 'y in BTerm } -->
   sequent { <H> >- 'x ~ 'y }

interactive var_neq_bterm 'H :
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in BTerm; <J['u]> >- 'l in nat } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in BTerm; <J['u]> >- 'r in nat } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in BTerm; <J['u]> >- 'depth in nat } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in BTerm; <J['u]> >- 'op in Operator } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in BTerm; <J['u]> >- 'subterms in list{BTerm} } -->
   sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in BTerm; <J['u]> >- 'C['u] }

interactive bterm_neq_var 'H :
   [wf] sequent { <H>; u: mk_bterm{'depth; 'op; 'subterms} = var{'l; 'r} in BTerm; <J['u]> >- 'l in nat } -->
   [wf] sequent { <H>; u: mk_bterm{'depth; 'op; 'subterms} = var{'l; 'r} in BTerm; <J['u]> >- 'r in nat } -->
   [wf] sequent { <H>; u: mk_bterm{'depth; 'op; 'subterms} = var{'l; 'r} in BTerm; <J['u]> >- 'depth in nat } -->
   [wf] sequent { <H>; u: mk_bterm{'depth; 'op; 'subterms} = var{'l; 'r} in BTerm; <J['u]> >- 'op in Operator } -->
   [wf] sequent { <H>; u: mk_bterm{'depth; 'op; 'subterms} = var{'l; 'r} in BTerm; <J['u]> >- 'subterms in list{BTerm} } -->
   sequent { <H>; u: mk_bterm{'depth; 'op; 'subterms} = var{'l; 'r} in BTerm; <J['u]> >- 'C['u] }

interactive subs_equal 'depth 'op :
   [wf] sequent { <H> >- 'depth in nat } -->
   [wf] sequent { <H> >- 'op in Operator } -->
   [wf] sequent { <H> >- 's1 in list{BTerm} } -->
   [wf] sequent { <H> >- 's2 in list{BTerm} } -->
   [aux] sequent { <H> >- compatible_shapes{'depth; shape{'op}; 's1} } -->
   [aux] sequent { <H> >- compatible_shapes{'depth; shape{'op}; 's2} } -->
   sequent { <H> >- mk_bterm{'depth; 'op; 's1} = mk_bterm{'depth; 'op; 's2} in BTerm } -->
   sequent { <H> >- 's1 = 's2 in list{BTerm} }

doc <:doc<
   << BTerm >> has a trivial squiggle equality.
>>
interactive bterm_sqsimple {| intro []; sqsimple |} :
   sequent { <H> >- sqsimple{BTerm} }

interactive bterm_sqsimple2 {| intro []; sqsimple |} :
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- sqsimple{BTerm{'n}} }

<:doc<
   Define a Boolean equality (alpha equality) on BTerms.
>>
define unfold_beq_bterm : beq_bterm{'t1; 't2} <-->
   fix{beq_bterm. lambda{t1. lambda{t2.
      dest_bterm{'t1;
         l1, r1.
            dest_bterm{'t2;
               l2, r2. beq_var{var{'l1; 'r1}; var{'l2; 'r2}};
               d1, o1, s1. bfalse};
         d1, o1, s1.
            dest_bterm{'t2;
               l2, r2. bfalse;
               d2, o2, s2.
                  band{beq_int{'d1; 'd2};
                  band{is_same_op{'o1; 'o2};
                  ball2{'s1; 's2; t1, t2. 'beq_bterm 't1 't2}}}}}}}} 't1 't2

let fold_beq_bterm = makeFoldC << beq_bterm{'t1; 't2} >> unfold_beq_bterm

interactive_rw reduce_beq_bterm_var_var {| reduce |} :
   'l1 in nat -->
   'r1 in nat -->
   'l2 in nat -->
   'r2 in nat -->
   beq_bterm{var{'l1; 'r1}; var{'l2; 'r2}}
   <-->
   beq_var{var{'l1; 'r1}; var{'l2; 'r2}}

interactive_rw reduce_beq_bterm_var_bterm {| reduce |} :
   'l in nat -->
   'r in nat -->
   'd in nat -->
   'o in Operator -->
   's in list{BTerm} -->
   compatible_shapes{'d; shape{'o}; 's} -->
   beq_bterm{var{'l; 'r}; mk_bterm{'d; 'o; 's}}
   <-->
   bfalse

interactive_rw reduce_beq_bterm_bterm_var {| reduce |} :
   'l in nat -->
   'r in nat -->
   'd in nat -->
   'o in Operator -->
   's in list{BTerm} -->
   compatible_shapes{'d; shape{'o}; 's} -->
   beq_bterm{mk_bterm{'d; 'o; 's}; var{'l; 'r}}
   <-->
   bfalse

interactive_rw reduce_beq_bterm_bterm_bterm {| reduce |} :
   'd1 in nat -->
   'o1 in Operator -->
   's1 in list{BTerm} -->
   'd2 in nat -->
   'o2 in Operator -->
   's2 in list{BTerm} -->
   compatible_shapes{'d1; shape{'o1}; 's1} -->
   compatible_shapes{'d2; shape{'o2}; 's2} -->
   beq_bterm{mk_bterm{'d1; 'o1; 's1}; mk_bterm{'d2; 'o2; 's2}}
   <-->
   band{beq_int{'d1; 'd2};
   band{is_same_op{'o1; 'o2};
   ball2{'s1; 's2; t1, t2. beq_bterm{'t1; 't2}}}}

interactive beq_bterm_wf {| intro [] |} :
   [wf] sequent { <H> >- 't1 in BTerm } -->
   [wf] sequent { <H> >- 't2 in BTerm } -->
   sequent { <H> >- beq_bterm{'t1; 't2} in bool }

interactive beq_bterm_intro {| intro [] |} :
   sequent { <H> >- 't1 = 't2 in BTerm } -->
   sequent { <H> >- "assert"{beq_bterm{'t1; 't2}} }

interactive beq_bterm_elim {| elim [] |} 'H :
   [wf] sequent { <H>; u: "assert"{beq_bterm{'t1; 't2}}; <J['u]> >- 't1 in BTerm } -->
   [wf] sequent { <H>; u: "assert"{beq_bterm{'t1; 't2}}; <J['u]> >- 't2 in BTerm } -->
   sequent { <H>; u: 't1 = 't2 in BTerm; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: "assert"{beq_bterm{'t1; 't2}}; <J['u]> >- 'C['u] }

(*
 * Equality on lists of BTerms.
 *)
define unfold_beq_bterm_list : beq_bterm_list{'l1; 'l2} <-->
   ball2{'l1; 'l2; t1, t2. beq_bterm{'t1; 't2}}

let fold_beq_bterm_list = makeFoldC << beq_bterm_list{'l1; 'l2} >> unfold_beq_bterm_list

interactive_rw reduce_beq_bterm_list_nil_nil {| reduce |} :
   beq_bterm_list{nil; nil}
   <-->
   btrue

interactive_rw reduce_beq_bterm_list_nil_cons {| reduce |} :
   beq_bterm_list{nil; 'u::'v}
   <-->
   bfalse

interactive_rw reduce_beq_bterm_list_cons_nil {| reduce |} :
   beq_bterm_list{'u::'v; nil}
   <-->
   bfalse

interactive_rw reduce_beq_bterm_list_cons_cons {| reduce |} :
   beq_bterm_list{'u1::'v1; 'u2::'v2}
   <-->
   band{beq_bterm{'u1; 'u2}; beq_bterm_list{'v1; 'v2}}

interactive beq_bterm_list_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l1 in list{BTerm} } -->
   [wf] sequent { <H> >- 'l2 in list{BTerm} } -->
   sequent { <H> >- beq_bterm_list{'l1; 'l2} in bool }

interactive beq_bterm_list_intro {| intro [] |} :
   sequent { <H> >- 't1 = 't2 in list{BTerm} } -->
   sequent { <H> >- "assert"{beq_bterm_list{'t1; 't2}} }

interactive beq_bterm_list_elim {| elim [] |} 'H :
   [wf] sequent { <H>; u: "assert"{beq_bterm_list{'t1; 't2}}; <J['u]> >- 't1 in list{BTerm} } -->
   [wf] sequent { <H>; u: "assert"{beq_bterm_list{'t1; 't2}}; <J['u]> >- 't2 in list{BTerm} } -->
   sequent { <H>; u: 't1 = 't2 in list{BTerm}; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: "assert"{beq_bterm_list{'t1; 't2}}; <J['u]> >- 'C['u] }

(************************************************************************
 * Forward-chaining.
 *)
doc <:doc<
   Simple rules for forward chaining.
>>
interactive beq_bterm_forward {| forward [] |} 'H :
   [wf] sequent { <H>; "assert"{beq_bterm{'t1; 't2}}; <J> >- 't1 in BTerm } -->
   [wf] sequent { <H>; "assert"{beq_bterm{'t1; 't2}}; <J> >- 't2 in BTerm } -->
   sequent { <H>; "assert"{beq_bterm{'t1; 't2}}; <J>; 't1 = 't2 in BTerm >- 'C } -->
   sequent { <H>; "assert"{beq_bterm{'t1; 't2}}; <J> >- 'C }

interactive beq_bterm_list_forward {| forward [] |} 'H :
   [wf] sequent { <H>; "assert"{beq_bterm_list{'t1; 't2}}; <J> >- 't1 in list{BTerm} } -->
   [wf] sequent { <H>; "assert"{beq_bterm_list{'t1; 't2}}; <J> >- 't2 in list{BTerm} } -->
   sequent { <H>; "assert"{beq_bterm_list{'t1; 't2}}; <J>; 't1 = 't2 in list{BTerm} >- 'C } -->
   sequent { <H>; "assert"{beq_bterm_list{'t1; 't2}}; <J> >- 'C }

(************************************************************************
 * Equality.
 *)
doc <:doc<
   Equality reasoning.
>>
interactive mk_bterm_simple_eq {| intro [] |} :
   [wf] sequent{ <H> >- 'd1 = 'd2 in nat } -->
   [wf] sequent{ <H> >- 'op1 = 'op2 in Operator } -->
   [wf] sequent{ <H> >- 'subterms1 = 'subterms2 in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'d1; shape{'op1}; 'subterms1} } -->
   sequent{ <H> >- mk_bterm{'d1; 'op1; 'subterms1} = mk_bterm{'d2; 'op2; 'subterms2} in BTerm }

interactive mk_bterm_eq {| intro [] |} :
   [wf] sequent{ <H> >- 'd1 = 'd3 in nat } -->
   [wf] sequent{ <H> >- 'd2 = 'd3 in nat } -->
   [wf] sequent{ <H> >- 'op1 = 'op2 in Operator } -->
   [wf] sequent{ <H> >- 'subterms1 = 'subterms2 in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'d1; shape{'op1}; 'subterms1} } -->
   sequent{ <H> >- mk_bterm{'d1; 'op1; 'subterms1} = mk_bterm{'d2; 'op2; 'subterms2} in BTerm{'d3} }

interactive bterm_depth_eq {| nth_hyp |} :
   sequent{ <H> >- 't in BTerm{'d} } -->
   sequent{ <H> >- 'd = bdepth{'t} in int }
