doc <:doc<
   @module[Itt_hoas_debruijn]
   The @tt[Itt_hoas_debruijn] module defines a mapping from de Bruijn-like
   representation of syntax into the HOAS.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

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

   Author: Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>

doc <:doc< @parents >>
extends Itt_hoas_base
extends Itt_hoas_vector
extends Itt_nat
extends Itt_list2

doc docoff

open Basic_tactics
open Itt_rfun

doc <:doc<
   @terms
   @modsubsection{A de Bruijn-like representation of syntax}
   Our de Bruijn-like representation of (bound) terms consists of two operators. <<var{'left; 'right}>>
   represents a variable bterm, whose ``left index'' is <<'left>> and whose ``right index'' is <<'right>>.
   Namely, it represent the term
   <<bind{x_1.math_ldots bind{x_left.bind{y.bind{z_1.math_ldots bind{z_right. 'v} math_ldots}}} math_ldots}>>.

   The <<mk_bterm{'n; 'op; 'btl}>> represents the compound term of depth $n$. In other words,
   <<mk_bterm{'n; 'op; (bind{'n; v.'bt_1['v]} :: math_ldots :: bind{'n; v.'bt_k['v]}::nil)}>> is
   <<bind{'n; v. mk_term{'op; ('bt_1['v] :: math_ldots :: 'bt_k['v]::nil)}}>>.
>>
define unfold_var:
   var{'left; 'right} <--> bind{'left; bind{v. bind{'right; 'v}}}

define (*private*) unfold_mk_bterm:
   mk_bterm{'n; 'op; 'btl}
   <-->
   ind{'n;
      lambda{btl. mk_term{'op; 'btl }};
      "_", r. lambda{btl. bind{v. 'r map{bt. subst{'bt; 'v}; 'btl}}}}
   'btl

doc <:doc<
   @modsubsection{Basic operations on syntax}
   <<bdepth{'bt}>> is the ``binding depth'' (i.e. the number of outer bindings) of a bterm <<'bt>>.

   <<left{'v}>> and <<right{'v}>> provide a way of computing the $l$ and $r$ indeces of a variable <<var{'l; 'r}>>.

   <<get_op{'bt; 'op}>> returns the <<'bt>>'s operator, if <<'bt>> is a @tt[mk_bterm] and returns
   <<'op>> if <<'bt>> is a variable.

   <<subterms{'bt}>> computes the subterms of the bterm <<'bt>>.
>>

define (*private*) unfold_bdepth:
   bdepth{'bt} <--> fix{f.lambda{bt. weak_dest_bterm{'bt; 1 +@ 'f subst{'bt; mk_term{it; nil}}; "_", "_". 0}}} 'bt

define (*private*) unfold_left:
   left{'bt} <-->
   fix{f.lambda{bt. lambda{l. weak_dest_bterm{'bt; 'f subst{'bt; mk_term{'l; nil}} ('l +@ 1); op, "_". 'op}}}} 'bt 0

define (*private*) unfold_right:
   right{'bt} <--> bdepth{'bt} -@ left{'bt} -@ 1

define (*private*) unfold_get_op:
   get_op{'bt; 'op} <--> fix{f.lambda{bt. weak_dest_bterm{'bt;  'f subst{'bt; mk_term{'op; nil}}; op, "_". 'op}}} 'bt

declare not_found

define iform unfold_get_op1:
   get_op{'bt} <--> get_op{'bt; not_found}

(*private*) define unfold_num_subterms:
   num_subterms{'bt}
   <-->
   fix{f. lambda{bt. weak_dest_bterm{'bt;  'f subst{'bt; mk_term{it; nil}}; "_", btl.  length{'btl}}}} 'bt

(*private*) define unfold_nth_subterm:
   nth_subterm{'bt; 'n}
   <-->
   fix{f. lambda{bt. weak_dest_bterm{'bt; bind{v. 'f subst{'bt; 'v}}; "_", btl. nth{'btl; 'n}}}} 'bt

define (*private*) unfold_subterms:
   subterms{'bt} <--> list_of_fun{n.nth_subterm{'bt; 'n}; num_subterms{'bt}}

doc <:doc< @rewrites >>

interactive_rw reduce_mk_bterm_base {| reduce |}:
   mk_bterm{0; 'op; 'btl} <--> mk_term{'op; 'btl }

interactive_rw reduce_mk_bterm_step {| reduce |}:
   'n in nat -->
   mk_bterm{'n +@ 1; 'op; 'btl} <--> bind{v. mk_bterm{'n; 'op; map{bt. subst{'bt; 'v}; 'btl}}}

interactive_rw reduce_mk_bterm_empty {| reduce |}:
   'n in nat -->
   mk_bterm{'n; 'op; nil} <--> bind{'n; mk_term{'op; nil}}

interactive_rw reduce_bdepth_mk_term {| reduce |}:
   bdepth{mk_term{'op; 'btl}} <--> 0

interactive_rw reduce_bdepth_bind {| reduce |} :
   bdepth{bind{v.'t['v]}} <--> 1 +@ bdepth{'t[mk_term{it; nil}]}

interactive_rw reduce_bdepth_var {| reduce |} :
   'l in nat -->
   'r in nat -->
   bdepth{var{'l; 'r}} <--> 'l +@ 'r +@ 1

interactive_rw reduce_bdepth_mk_bterm {| reduce |} :
   'n in nat -->
   bdepth{mk_bterm{'n; 'op; 'btl}} <--> 'n

interactive_rw reduce_getop_var {| reduce |} :
   'l in nat -->
   'r in nat -->
   get_op{var{'l; 'r}; 'op} <--> 'op

interactive_rw reduce_getop_mkbterm {| reduce |} :
   'n in nat -->
   get_op{mk_bterm{'n; 'op; 'btl}; 'op'} <--> 'op

interactive_rw num_subterms_id {| reduce |} :
   'btl in list -->
   'n in nat -->
   num_subterms{mk_bterm{'n; 'op; 'btl}} <--> length{'btl}

interactive_rw nth_subterm_id {| reduce |} :
   'n in nat -->
   'm in nat -->
   'k in nat -->
   'k < 'm -->
   nth_subterm{mk_bterm{'n; 'op; list_of_fun{x.'f['x]; 'm}}; 'k} <--> bind{'n; v. substl{'f['k]; 'v}}

interactive_rw subterms_id {| reduce |} :
   'btl in list -->
   'n in nat -->
   subterms{mk_bterm{'n; 'op; 'btl}} <--> map{bt. bind{'n; v. substl{'bt; 'v}}; 'btl}

interactive_rw left_id {| reduce |} :
   'l in nat -->
   'r in nat -->
   left{var{'l; 'r}} <--> 'l

interactive_rw right_id {| reduce |} :
   'l in nat -->
   'r in nat -->
   right{var{'l; 'r}} <--> 'r

interactive_rw subst_var0 {| reduce |} :
   'r in nat -->
   subst{var{0; 'r};'t} <--> bind{'r;'t}

interactive_rw subst_var {| reduce |} :
   'l in nat -->
   'r in nat -->
   subst{var{'l+@1; 'r};'t} <--> var{'l;'r}

interactive_rw subst_mkbterm {| reduce |} :
   'bdepth in nat -->
   subst{mk_bterm{'bdepth+@1;'op;'btl};'t} <-->  mk_bterm{'bdepth; 'op; map{bt. subst{'bt; 't}; 'btl}}

interactive_rw bind_var {| reduce |} :
   'l in nat -->
   'r in nat -->
   bind{x.var{'l; 'r}} <--> var{'l+@1;'r}

interactive_rw lemma {| reduce |} :
   'btl in list -->
   map{bt. subst{'bt; 'v}; map{bt. bind{x. 'bt}; 'btl}} <--> 'btl

interactive_rw bind_mkbterm  {| reduce |} :
   'bdepth in nat -->
   'btl in list -->
   bind{x.mk_bterm{'bdepth;'op;'btl}} <-->  mk_bterm{'bdepth+@1; 'op; map{bt. bind{x.'bt}; 'btl}}

doc docoff

dform var_df : var{'l; 'r} =
   pushm[3] tt["var"] `"(" slot{'l} `"," slot{'r} `")" popm

dform mk_bterm_df : mk_bterm{'n; 'op; 'btl} =
   szone pushm[3] tt["mk_bterm"] `"(" slot{'n} `";" hspace slot{'op} `";" hspace slot{'btl} `")" popm ezone

dform bdepth_df: parens :: "prec"[prec_apply] :: bdepth{'bt} =
   tt["D"] space slot["le"]{'bt}

dform left_df: parens :: "prec"[prec_apply] :: left{'bt} =
   tt["l"] space slot["le"]{'bt}

dform right_df: parens :: "prec"[prec_apply] :: right{'bt} =
   tt["r"] space slot["le"]{'bt}

dform get_op_df: get_op{'bt; 'op} =
   pushm[0] szone pushm[3] keyword["try"] hspace tt["get_op"] space slot{'bt}
   popm hspace pushm[3] keyword["with"] tt[" Not_found ->"] hspace slot{'op} popm ezone popm

dform subterms_df: "prec"[prec_apply] :: parens :: subterms{'bt} =
   tt["subterms"] space slot["le"]{'bt}
