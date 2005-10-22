
doc <:doc<
   @module[Itt_hoas_lang]
   The @tt[Itt_hoas_lang] module defines the type of a language over
   a list of operators.

   If <<'sop>> is a subtype of <<Operator>>, then <<Lang{'sop}>> is the
   type that contains all terms built with operators in <<'sop>>.


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
extends Itt_hoas_destterm
extends Itt_image
extends Itt_tunion
extends Itt_list2
extends Itt_subset2
doc docoff

open Basic_tactics

doc terms

doc <:doc<
     We define the type <<Lang{'sop}>> as the recursive type.

>>
define iform unfold_SubOp : SubOp{'ops} <--> listmem_set{'ops; Operator}

define unfold_compatible_shapes: compatible_shapes{'bdepth; 'op; 'btl} <-->
      length{shape{'op}} = length{'btl} in int &
      all i:Index{'btl}. bdepth{nth{'btl;'i}} =  'bdepth +@ nth{shape{'op};'i} in int

define unfold_Ldom: dom{'sop; 'BT} <--> nat*nat + depth:nat * op: 'sop * {subterms:list{'BT} | compatible_shapes{'depth;'op;'subterms} }

define unfold_mk: mk{'x} <--> decide{'x;
                                      v.spread{'v;left,right. var{'left;'right}};
                                      t.spread{'t;d,op,st. mk_bterm{'d;'op;'st}}}

define unfold_dest: dest{'bt} <--> dest_bterm{'bt; l,r. inl{('l,'r)}; d,op,ts. inr{('d,('op,'ts))}}

define unfold_LIter: Iter{'sop; 'X} <--> Img{dom{'sop; 'X};x.mk{'x}}

define unfold_LBT: BT{'sop; 'n} <--> ind{'n; void; X.Iter{'sop; 'X}}

define unfold_Lang: Lang{'sop} <--> Union n:nat. BT{'sop; 'n}

define iform unfold_BTerm: BTerm <--> Lang{Operator}


define (*privite *) unfold_ndepth:
   ndepth{'t} <-->
    fix{ndepth. lambda{t.
      dest_bterm{'t; l,r.1; bdepth,op,subterms. list_max{map{x.'ndepth 'x;'subterms}}+@ 1 }
    }} 't

let fold_ndepth = makeFoldC << ndepth{'t} >> unfold_ndepth

doc docoff

let fold_Ldom = makeFoldC << dom{'sop; 'BT} >> unfold_Ldom
let fold_mk = makeFoldC << mk{'x} >> unfold_mk
let fold_dest = makeFoldC << dest{'bt} >> unfold_dest
let fold_LIter = makeFoldC << Iter{'sop; 'X} >> unfold_LIter
let fold_Lang = makeFoldC << Lang{'sop} >> unfold_Lang

doc rules

interactive_rw lbt_reduce_base {| reduce |}: BT{'sop; 0} <--> void

interactive_rw lbt_reduce_step {| reduce |}: 'n in nat --> BT{'sop; 'n+@1} <--> Iter{'sop; BT{'sop; 'n}}

interactive  lbt_elim_squash  {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'n in nat } -->
   [base] sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   [step] sequent { <H>; <J>; depth: nat; op:'sop; subterms:list{BT{'sop; 'n}};
             compatible_shapes{'depth;'op;'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BT{'sop; 'n+@1}; <J> >- squash{'P['t]} }

interactive  lbt_elim_squash0  {| nth_hyp |} 'H :
   sequent { <H>; t: BT{'sop; 0}; <J> >- 'P['t] }

interactive  lbt_wf_and_bdepth_wf  {| intro[] |}:
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- BT{'sop; 'n} Type & all t: BT{'sop; 'n}. bdepth{'t} in nat }

interactive  lbt_wf {| intro[] |}:
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- BT{'sop; 'n} Type }

interactive lang_wf  {| intro[] |} :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- Lang{'sop} Type }

(* Should be:
interactive  bdepth_wf  {| intro[intro_typeinf <<'t>>] |} Lang{'sop} :
*)
interactive  bdepth_wf  {| intro[] |} 'sop :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent{ <H> >- 't in Lang{'sop} } -->
   sequent{ <H> >- bdepth{'t} in nat }

(*interactive compatible_shapes_wf {| intro[] |} 'sop 'n :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 'bdepth in nat } -->
   sequent { <H> >- 'op in 'sop } -->
   sequent { <H> >- 'btl in list{BT{'sop; 'n}} } -->
   sequent { <H> >- compatible_shapes{'bdepth; 'op; 'btl} Type }
*)
(* SHould be:
interactive compatible_shapes_wf {| intro[intro_typeinf <<'op>>] |} 'sop :
*)
interactive compatible_shapes_wf {| intro[] |} 'sop :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'bdepth in nat } -->
   sequent { <H> >- 'op in 'sop } -->
   sequent { <H> >- 'btl in list{Lang{'sop}} } -->
   sequent { <H> >- compatible_shapes{'bdepth; 'op; 'btl} Type }

interactive compatible_shapes_depth {| intro[] |} 'sop 'op 'i :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'bdepth in nat } -->
   sequent { <H> >- 'op in 'sop } -->
   sequent { <H> >- 'btl in list{Lang{'sop}} } -->
   sequent { <H> >- compatible_shapes{'bdepth; 'op; 'btl} } -->
   sequent { <H> >- 'i in Index{'btl} } -->
   sequent { <H> >- 'bdepth <= bdepth{nth{'btl; 'i}} }

interactive compatible_shapes_depth2 {| intro[] |} 'sop 'op 'i :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'bdepth in nat } -->
   sequent { <H> >- 'op in 'sop } -->
   sequent { <H> >- 'btl in list{Lang{'sop}} } -->
   sequent { <H> >- compatible_shapes{'bdepth; 'op; 'btl} } -->
   sequent { <H> >- 'i in Index{'btl} } -->
   sequent { <H> >- bdepth{nth{'btl; 'i}} >= 'bdepth }

interactive  lbt_subtype_lang  {| intro[] |} :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'sop; 'n} subtype Lang{'sop} }

interactive ldom_wf1 {| intro[] |}:
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >-  dom{'sop; BT{'sop; 'n}} Type }

interactive compatible_shapes_sqstable (*{| squash |}*) :
   sequent{ <H> >- 'btl in list } -->
   sequent{ <H> >- squash{compatible_shapes{'bdepth; 'op; 'btl}}  } -->
   sequent{ <H> >- compatible_shapes{'bdepth; 'op; 'btl} }

interactive ldom_wf {| intro[] |}:
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'T subtype Lang{'sop} } -->
   sequent { <H> >-  dom{'sop; 'T} Type }

interactive dom_monotone {| intro[] |}:
   [wf] sequent { <H> >- 'sop subtype Operator } -->
   sequent{ <H> >- 'T subtype 'S } -->
   sequent { <H> >- 'S subtype Lang{'sop} } -->
   sequent{ <H> >-  dom{'sop;'T} subtype dom{'sop;'S} }

interactive dom_monotone_set {| intro[] |}:
   [wf] sequent { <H> >- 'sop subtype Operator } -->
   sequent{ <H> >- 'T subset 'S } -->
   sequent { <H> >- 'S subtype Lang{'sop} } -->
   sequent{ <H> >-  dom{'sop;'T} subset dom{'sop;'S} }

interactive iter_monotone {| intro[] |}:
   [wf] sequent { <H> >- 'sop subtype Operator } -->
   sequent{ <H> >- 'T subtype 'S } -->
   sequent { <H> >- 'S subtype Lang{'sop} } -->
   sequent{ <H> >-  Iter{'sop;'T} subtype Iter{'sop;'S} }


(*interactive  lbt_subtype_bt  {| intro[] |} :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'sop; 'n} subtype BT{'n} }

interactive lang_subtype  {| intro[] |} :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- Lang{'sop} subtype BTerm }

interactive  lbt_subtype_bterm  {| intro[] |} :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'sop; 'n} subtype BTerm }
*)

interactive  lbt_subtype_bterm  {| intro[] |} :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'sop; 'n} subtype Lang{'sop} }

interactive lbt_monotone  {| intro[] |} :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'sop; 'n} subtype BT{'sop; 'n+@1} }

interactive lang_intro_var0 {| intro[] |}:
   sequent { <H> >- 'X subtype Lang{'sop} } -->
   sequent { <H> >- 'l in nat } -->
   sequent { <H> >- 'r in nat } -->
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- var{'l;'r} in Iter{'sop;'X} }

interactive lang_intro_var {| intro[] |}:
   sequent { <H> >- 'l in nat } -->
   sequent { <H> >- 'r in nat } -->
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- var{'l;'r} in Lang{'sop} }

interactive lbt_intro_mk_bterm {| intro[] |}:
   sequent { <H> >- 'sop subtype Operator } -->
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- 'depth in nat } -->
   sequent{ <H> >- 'op in 'sop } -->
   sequent{ <H> >- 'subterms in list{BT{'sop; 'n}} } -->
   sequent{ <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth;'op;'subterms} in BT{'sop; 'n+@1} }
(*
interactive lang_intro_mk_bterm_wf0 {| intro[] |}:
   sequent { <H> >- 'X subtype Lang{'sop} } -->
   sequent { <H> >- 'sop subtype Operator } -->
   sequent{ <H> >- 'depth in nat } -->
   sequent{ <H> >- 'op in 'sop } -->
   sequent{ <H> >- 'subterms in list{'X} } -->
   sequent{ <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth;'op;'subterms} in Iter{'sop;'X} }
*)
interactive lang_intro_mk_bterm_wf1 {| intro[] |}:
   sequent { <H> >- 'sop subtype Operator } -->
   sequent{ <H> >- 'depth in nat } -->
   sequent{ <H> >- 'op in 'sop } -->
   sequent{ <H> >- 'subterms in list{Lang{'sop}} } -->
   sequent{ <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth;'op;'subterms} in Lang{'sop} }

interactive lang_intro_mk_bterm_wf2 {| intro[] |}:
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'depth in nat } -->
   sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- 'subterms in list{Lang{SubOp{'ops}}} } -->
   sequent { <H> >- mem{'op;'ops;Operator}  } -->
   sequent { <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent { <H> >- mk_bterm{'depth;'op;'subterms} in Lang{SubOp{'ops}} }

interactive  lbt_elim_squash1  {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'n in nat } -->
   [wf] sequent { <H>; <J> >- 'sop subtype Operator } -->
   [base] sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   [step] sequent { <H>; 'n>0; <J>; depth: nat; op: 'sop; subs: list{BT{'sop; 'n-@1}};
               compatible_shapes{'depth;'op;'subs} >- squash{'P[mk_bterm{'depth;'op;'subs}]} } -->
   sequent { <H>; t: BT{'sop; 'n}; <J> >- squash{'P['t]} }

interactive  lang_elim_squash {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'sop subtype Operator } -->
   sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   sequent { <H>; <J>; n:nat;
                depth: nat; op: 'sop; subs: list{BT{'sop;'n}};
                compatible_shapes{'depth;'op;'subs};
                all_list{'subs;t.squash{'P['t]}}
                >- squash{'P[mk_bterm{'depth;'op;'subs}]} } -->
   sequent { <H>; t: Lang{'sop}; <J> >- squash{'P['t]} }


(* ???????????? *)
interactive_rw bind_eta 'sop :
   'bt in Lang{'sop} -->
   bdepth{'bt} > 0 -->
   'sop subtype Operator -->
   bind{x. subst{'bt; 'x}} <--> 'bt

interactive_rw bind_vec_eta 'sop :
   'n in nat -->
   'bt in Lang{'sop} -->
    bdepth{'bt} >= 'n -->
   'sop subtype Operator -->
    bind{'n; gamma. substl{'bt; 'gamma}} <--> 'bt

interactive_rw subterms_lemma 'sop :
   'n in nat -->
   'subterms in list{Lang{'sop}} -->
   all i:Index{'subterms}. bdepth{nth{'subterms;'i}} >=  'n -->
   'sop subtype Operator -->
   map{bt. bind{'n; v. substl{'bt; 'v}};'subterms} <--> 'subterms

interactive_rw dest_bterm_mk_bterm2 'sop :
   'n in nat -->
   'op in 'sop -->
   'subterms in list{Lang{'sop}} -->
   compatible_shapes{'n;'op;'subterms} -->
   'sop subtype Operator -->
   dest_bterm{mk_bterm{'n; 'op; 'subterms}; l,r.'var_case['l; 'r]; bdepth,op,subterms. 'op_case['bdepth; 'op; 'subterms] }
   <-->
   'op_case['n; 'op; 'subterms]

(* ???????????? *)

interactive lang_monotone {| intro[] |}:
   sequent { <H> >- 'sop1 subtype 'sop2 } -->
   sequent { <H> >- 'sop2 subtype Operator } -->
   sequent { <H> >- Lang{'sop1} subtype Lang{'sop2} }

interactive lang_is_btrem {| intro[intro_typeinf <<'t>>] |} <<Lang{'sop}>> :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 't in Lang{'sop} } -->
   sequent { <H> >- 't in BTerm }


interactive iter_monotone_set {| intro[] |}:
   [wf] sequent { <H> >- 'sop subtype Operator } -->
   sequent{ <H> >- 'T subset 'S } -->
   sequent { <H> >- 'S subtype Lang{'sop} } -->
   sequent{ <H> >-  Iter{'sop;'T} subset Iter{'sop;'S} }

interactive lbt_monotone_set  {| intro[] |} :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'sop; 'n} subset BT{'sop; 'n+@1} }

interactive lbt_monotone_set2  {| intro[] |} :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'k in nat} -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >- 'k <= 'n} -->
   sequent { <H> >- BT{'sop; 'k} subset BT{'sop; 'n} }


interactive_rw reduce_ndepth1 {| reduce |}:
   ('l in nat) -->
   ('r in nat) -->
   ndepth{var{'l;'r}} <--> 1

interactive_rw reduce_ndepth2 {| reduce |}:
   'op in Operator -->
   'bdepth in nat -->
   'subs in list{BTerm} -->
   compatible_shapes{'bdepth;'op;'subs} -->
   ndepth{mk_bterm{'bdepth;'op;'subs}} <--> list_max{map{x.ndepth{'x};'subs}}+@ 1


interactive ndepth_wf {| intro[] |}:
   sequent{ <H> >- 't in BTerm } -->
   sequent { <H> >-  ndepth{'t} in nat }
(*
interactive ndepth_less {| intro[intro_typeinf <<'t>>] |} <<BT{'sop;'m}>> :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- 'm in nat } -->
   sequent{ <H> >- 'm <= 'n } -->
   sequent{ <H> >- 't in BT{'sop; 'm} } -->
   sequent { <H> >-  ndepth{'t} <= 'n }
*)
interactive ndepth_correct {| intro[] |} :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent{ <H> >- 't in Lang{'sop} } -->
   sequent { <H> >-  't in BT{'sop; ndepth{'t}} }


interactive  lbt_subset_bterm  {| intro[] |} :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H> >- 'n in nat} -->
   sequent { <H> >- BT{'sop; 'n} subset Lang{'sop} }



interactive  lang_elim_sq {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'sop subtype Operator } -->
   sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   sequent { <H>; <J>; n:nat;
                depth: nat; op: 'sop; subs: list{Lang{'sop}};
                compatible_shapes{'depth;'op;'subs};
                all_list{'subs;t.squash{'P['t]}}
                >- squash{'P[mk_bterm{'depth;'op;'subs}]} } -->
   sequent { <H>; t: Lang{'sop}; <J> >- squash{'P['t]} }



interactive_rw mk_dest_reduce 'sop :
   'sop subtype Operator -->
   't in Lang{'sop}  -->
   mk{dest{'t}} <--> 't

(* Should be:
interactive dest_bterm_wf {| intro[intro_typeinf <<'bt>>] |} Lang{'sop} :
*)
interactive dest_bterm_wf {| intro[] |} 'sop :
   sequent { <H> >- 'sop subtype Operator } -->
   sequent{ <H> >- 'bt in Lang{'sop} } -->
   sequent{ <H>; l:nat; r:nat >- 'var_case['l;'r] in 'T } -->
   sequent{ <H>; bdepth: nat; op: 'sop; subterms: list{Lang{'sop}};
                 compatible_shapes{'bdepth;'op;'subterms} >- 'op_case['bdepth; 'op; 'subterms] in 'T } -->
   sequent{ <H> >- dest_bterm{'bt; l,r.'var_case['l; 'r]; bdepth,op,subterms. 'op_case['bdepth; 'op; 'subterms]} in 'T }

interactive dest_wf {| intro[] |}:
   sequent { <H> >- 'sop subtype Operator } -->
   sequent{ <H> >- 't in Lang{'sop} } -->
   sequent{ <H> >-  dest{'t} in dom{'sop; Lang{'sop}} }

interactive  lbt_elim_squash2  {| elim [] |} 'H :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'sop subtype Operator } -->
   [base] sequent { <H>; t: BT{'sop; 'n+@1}; <J['t]>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   [step] sequent { <H>; t: BT{'sop; 'n+@1}; <J['t]>; depth: nat; op: 'sop; subs: list{BT{'sop; 'n}};
                compatible_shapes{'depth;'op;'subs} >- squash{'P[mk_bterm{'depth;'op;'subs}]} } -->
   sequent { <H>; t: BT{'sop; 'n+@1}; <J['t]> >- squash{'P['t]} }

interactive ldom_elim  {| elim [] |} 'H :
   sequent { <H>; t: dom{'sop; 'T}; u: nat*nat; <J[inl{'u}]> >- 'P[inl{'u}] } -->
   sequent { <H>; t: dom{'sop;'T}; v: depth:nat * op:'sop * {subterms:list{'T} | compatible_shapes{'depth;'op;'subterms}}; <J[inr{'v}]>
               >- 'P[inr{'v}] } -->
   sequent { <H>; t: dom{'sop;'T}; <J['t]> >- 'P['t] }

interactive_rw dest_mk_reduce BT{'sop; 'n} :
   'sop subtype Operator -->
   'n in nat -->
   't in dom{'sop; BT{'sop; 'n}}  -->
   dest{mk{'t}} <--> 't

interactive  lbt_elim1  {| elim [] |} 'H :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'sop subtype Operator } -->
   [step] sequent { <H>; t: BT{'sop; 'n+@1}; <J['t]>; x: dom{'sop; BT{'sop; 'n}} >- 'P[mk{'x}] } -->
   sequent { <H>; t: BT{'sop; 'n+@1}; <J['t]> >- 'P['t] }

interactive  lang_elim_squash1 {| elim [] |} 'H :
   [wf] sequent { <H> >- 'sop subtype Operator } -->
   sequent { <H>; t: Lang{'sop}; <J['t]>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   sequent { <H>; t: Lang{'sop}; <J['t]>; depth: nat; op: 'sop; subs: list{Lang{'sop}};
               compatible_shapes{'depth;'op;'subs} >- squash{'P[mk_bterm{'depth;'op;'subs}]} } -->
   sequent { <H>; t: Lang{'sop}; <J['t]> >- squash{'P['t]} }


interactive lang_elim  'H :
   [wf] sequent { <H>; <J> >- 'sop subtype Operator } -->
   sequent { <H>; <J>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; <J>; bdepth: nat; op: 'sop; subs: list{Lang{'sop}};
               compatible_shapes{'bdepth;'op;'subs};
               all_list{'subs;t.'P['t]}
               >- 'P[mk_bterm{'bdepth;'op;'subs}] } -->
   sequent { <H>; t: Lang{'sop}; <J> >- 'P['t] }

(*
 * The previous rule does not conform to the usual induction standard,
 * which makes it hard to use because the hyp must usually be the last
 * one in the sequent.  Instead, use this rule, which allows induction
 * on any sequent.  Note that it does not increase the expressive power,
 * it just makes the rule easier to use.
 *)
interactive lang_elim2 {| elim [] |} 'H :
   [wf] sequent { <H>; t: Lang{'sop}; <J['t]> >- 'sop subtype Operator } -->
   sequent { <H>; t: Lang{'sop}; <J['t]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; t: Lang{'sop}; <J['t]>;
               bdepth: nat; op: 'sop; subs: list{Lang{'sop}};
               compatible_shapes{'bdepth; 'op; 'subs};
               all_list{'subs; t. 'P['t]}
               >- 'P[mk_bterm{'bdepth; 'op; 'subs}]
           } -->
   sequent { <H>; t: Lang{'sop}; <J['t]> >- 'P['t] }

interactive lang_induction  {| elim [] |} 'H :
   [wf] sequent { <H> >- 'sop subtype Operator } -->
   [base] sequent { <H>; t: Lang{'sop}; <J['t]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   [step] sequent { <H>; t: Lang{'sop}; <J['t]>; bdepth: nat; op: 'sop; subs: list{Lang{'sop}};
               compatible_shapes{'bdepth;'op;'subs} >- 'P[mk_bterm{'bdepth;'op;'subs}] } -->
   sequent { <H>; t: Lang{'sop}; <J['t]> >- 'P['t] }

interactive lang_induction2  {| elim [] |} 'H :
   [wf] sequent { <H> >- 'h in Operator } -->
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H>; t: Lang{SubOp{'h::'ops}}; <J['t]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; t: Lang{SubOp{'h::'ops}}; <J['t]>; bdepth: nat; subs: list{Lang{SubOp{'h::'ops}}};
               compatible_shapes{'bdepth;'h;'subs} >- 'P[mk_bterm{'bdepth;'h;'subs}] } -->
   sequent { <H>; t: Lang{SubOp{'h::'ops}}; <J['t]>; bdepth: nat; op: SubOp{'ops}; subs: list{Lang{SubOp{'h::'ops}}};
               compatible_shapes{'bdepth;'op;'subs} >- 'P[mk_bterm{'bdepth;'op;'subs}] } -->
   sequent { <H>; t: Lang{SubOp{'h::'ops}}; <J['t]> >- 'P['t] }

doc docoff

dform lang_df: Lang{'op} =
   tt["Language"] `"[" slot{'op} `"]"

