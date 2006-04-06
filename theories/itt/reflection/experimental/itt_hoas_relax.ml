doc <:doc<
   @module[Itt_hoas_relax]

   The @tt[Itt_hoas_relax] module defines some transformations
   with relaxed wf subgoals.

   The goal here is to define a type << Bind{'n} >> that includes
   all the terms with binding depth at least << 'n >>.  We will have
   << BTerm{'n} subtype Bind{'m} >> if << 'n >= 'm >>.
   It will also follow that any term of the form
   << bind{'n; x. math_ldots} >> will be in the << Bind{'n} >> type.

   We can then show the eta-rules for << Bind{'n} >> terms, and
   then a corresponding rule for
   << dest_bterm{'e; l, r. 'base['l; 'r]; d, o, s. 'step['d; 'o; 's]} >>
   that uses relaxed terms.

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}

   @end[license]
   @parents
>>
extends Itt_hoas_bterm
extends Itt_hoas_vbind
extends Itt_vec_list1
extends Itt_match

doc docoff

open Basic_tactics

(*
 * Select option for this theory.
 *)
declare relax : SelectOption

let relax_term   = << select["relax":t] >>
let relax_option = [relax_term]

(*
 * By default reject the resource.
 * Privately, accept it.
 *)
let resource select +=
   relax_term, OptionExclude

let resource private select +=
   relax_term, OptionAllow

(************************************************************************
 * General Bind type.
 *)
doc <:doc<
   Define a type << Bind{'n} >> that includes all values
   with binding depth at least << 'n >>.
>>
define unfold_BindInfo : BindInfo{'n} <--> <:xterm<
   { i: nat | i = n in nat } * ({ l : list{top} | length{l} = n in nat } -> top)
>>

define unfold_bind_of_info : bind_of_info{'x} <--> <:xterm<
   let n, f = x in
      bind{n; y. f y}
>>

define unfold_Bind : Bind{'n} <--> <:xterm<
   Img{BindInfo{n}; f. bind_of_info{f}}
>>

(************************************************************************
 * Well-formedness.
 *)
doc <:doc<
   Well-formedness of the << Bind{'n} >> type.
>>
interactive bind_info_wf {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- BindInfo{n} Type
>>

interactive bind_wf {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- Bind{n} Type
>>

interactive bind_of_info_wf {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- x in BindInfo{n} -->
   <H> >- bind_of_info{x} in Bind{n}
>>

interactive pair_in_bind_info {| intro |} : <:xrule<
   "wf" : <H> >- i = n in nat -->
   "wf" : <H> >- f in { l : list{top} | length{l} = n in nat } -> top -->
   <H> >- (i, f) in BindInfo{n}
>>

(************************************************************************
 * Rewrites.
 *)
interactive_rw reduce_bind_of_info {| reduce |} : <:xrewrite<
   bind_of_info{(n, f)}
   <-->
   bind{n; y. f y}
>>

(************************************************************************
 * More well-formedness.
 *)
doc <:doc<
   More well-formedness.
>>
interactive bind_in_bind_eq {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- bind{n; y. e[y]} in Bind{n}
>>

interactive bind_in_bind_ge : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- m in nat -->
   "wf" : <H> >- n >= m -->
   <H> >- bind{n; y. e[y]} in Bind{m}
>>

interactive bind_in_bind_add {| intro |} : <:xrule<
   "wf" : <H> >- m in nat -->
   "wf" : <H> >- k in nat -->
   <H> >- bind{m +@ k; y. e[y]} in Bind{m}
>>

interactive bind_monotone 'n : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- m in nat -->
   "wf" : <H> >- n >= m -->
   "wf" : <H> >- e in Bind{n} -->
   <H> >- e in Bind{m}
>>

(************************************************************************
 * Relaxed rewrites.
 *)
doc <:doc<
   Relaxed eta-reductions.
>>
interactive_rw bind_eta_relax {| reduce ~labels:relax_option |} : <:xrewrite<
   t in Bind{1} -->
   bind{x. subst{t; x}}
   <-->
   t
>>

interactive_rw bindn_eta_relax {| reduce ~labels:relax_option |} : <:xrewrite<
   n in nat -->
   t in Bind{n} -->
   bind{n; x. substl{t; x}}
   <-->
   t
>>

(************************************************************************
 * Relation to BTerms.
 *)
doc <:doc<
   All terms in << BTerm{'n} >> are in << Bind{'n} >> if
   << 'm >= 'n >>.
>>
interactive bind0_is_top {| intro |} : <:xrule<
   <H> >- e in Bind{0}
>>

interactive var_is_bind {| intro |} : <:xrule<
   "wf" : <H> >- l in nat -->
   "wf" : <H> >- r in nat -->
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- l +@ r +@ 1 >= n -->
   <H> >- var{l; r} in Bind{n}
>>

interactive_rw reduce_mk_bterm_full_lof : <:xrewrite<
   n in nat -->
   m in nat -->
   mk_bterm{n; op; list_of_fun{i. f[i]; m}}
   <-->
   bind{n; x. mk_term{op; list_of_fun{i. substl{f[i]; x}; m}}}
>>

interactive_rw reduce_mk_bterm_full : <:xrewrite<
   n in nat -->
   subterms in list -->
   mk_bterm{n; op; subterms}
   <-->
   bind{n; x. mk_term{op; map{subterm. substl{subterm; x}; subterms}}}
>>

interactive mk_bterm_is_bind {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- m in nat -->
   "wf" : <H> >- n >= m -->
   "wf" : <H> >- subterms in list -->
   <H> >- mk_bterm{n; op; subterms} in Bind{m}
>>

interactive bterm_is_bind 'n : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- m in nat -->
   "wf" : <H> >- n >= m -->
   "wf" : <H> >- e in BTerm{n} -->
   <H> >- e in Bind{m}
>>

interactive bterm_is_bind2 {| nth_hyp |} 'H : <:xrule<
   "wf" : <H>; b: BTerm{n}; <J[b]> >- n in nat -->
   <H>; b: BTerm{n}; <J[b]> >- b in Bind{n}
>>

(************************************************************************
 * Relaxed reductions.
 *)
doc <:doc<
   Restate theorems from @tt[Itt_hoas_bterm].
>>
interactive_rw subterms_lemma_relax {| reduce ~labels:relax_option |} : <:xrewrite<
   n in nat -->
   subterms in list{Bind{n}} -->
   map{bt. bind{n; v. substl{bt; v}}; subterms}
   <-->
   subterms
>>

doc <:doc<
   This is the key rule, where we relax the reduction
   << dest_bterm{'e; l, r. 'base; d, o, s. 'step} >>.
>>
interactive_rw dest_bterm_mk_bterm_relax {| reduce ~labels:relax_option |} : <:xrewrite<
   n in nat -->
   op in Operator -->
   subterms in list{Bind{n}} -->
   "dest_bterm"{mk_bterm{n; op; subterms}; l, r. var_case[l; r]; d, o, s. op_case[d; o; s] }
   <-->
   op_case[n; op; subterms]
>>

(************************************************************************
 * Triangle type.
 *)
doc <:doc<
   The << BindTriangle{'n} >> type defines lists of terms with
   increasing binding depth.
>>
define unfold_BindTriangleInfo : BindTriangleInfo{'n} <--> <:xterm<
   { i: nat | i = n in nat }
   * Prod len: nat
   * (Fun j: ({ k : nat | k < len }) -> Bind{j +@ n})
>>

define unfold_bind_triangle_of_info : bind_triangle_of_info{'x} <--> <:xterm<
   let n, len, f = x in
      list_of_fun{i. f i; len}
>>

define unfold_BindTriangle : BindTriangle{'n} <--> <:xterm<
   Img{BindTriangleInfo{n}; f. bind_triangle_of_info{f}}
>>

(************************************************
 * Well-formedness.
 *)
doc <:doc<
   Well-formedness.
>>
interactive bind_triangle_info_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- BindTriangleInfo{n} Type
>>

interactive bind_triangle_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- BindTriangle{n} Type
>>

(************************************************
 * Reductions.
 *)
interactive_rw reduce_bind_triangle_of_triple {| reduce |} : <:xrule<
   bind_triangle_of_info{(n, (len, f))}
   <-->
   list_of_fun{i. f i; len}
>>

interactive bind_triangle_is_list1 'n : <:xrule<
   "wf" : <H> >- l in BindTriangle{n} -->
   <H> >- l in list
>>

interactive bind_triangle_is_list2 {| nth_hyp |} 'H : <:xrule<
   <H>; l: BindTriangle{n}; <J[l]> >- l in list
>>

(************************************************
 * Equality.
 *)
interactive_rw bind_triangle_of_info_eq <:xterm< bind_triangle_of_info{(n2, (m2, f2))} >> : <:xrewrite<
   n1 = n2 in nat -->
   m1 = m2 in nat -->
   all i: nat. (i < m1 => f1 i ~ f2 i) -->
   bind_triangle_of_info{(n1, (m1, f1))}
   <-->
   bind_triangle_of_info{(n2, (m2, f2))}
>>

interactive_rw bind_triangle_of_info_step : <:xrewrite<
   m in nat -->
   bind_triangle_of_info{(n, (m +@ 1, f))}
   <-->
   f 0 :: bind_triangle_of_info{(n +@ 1, (m, lambda{i. 'f ('i +@ 1)}))}
>>

(************************************************
 * Intro/elim.
 *)
doc <:doc<
   Introduction and elimination reasoning.
>>
interactive bind_triangle_of_info_wf {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- x in BindTriangleInfo{n} -->
   <H> >- bind_triangle_of_info{x} in BindTriangle{n}
>>

interactive nil_bind_triangle_wf {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- [] in BindTriangle{n}
>>

interactive cons_bind_triangle_wf {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- u in Bind{n} -->
   "wf" : <H> >- v in BindTriangle{n +@ 1} -->
   <H> >- u::v in BindTriangle{n}
>>

interactive bind_triangle_length_wf 'n : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- l in BindTriangle{n} -->
   <H> >- length{l} in nat
>>

interactive bind_hd_wf : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- l in BindTriangle{n} -->
   "wf" : <H> >- length{l} > 0 -->
   <H> >- hd{l} in Bind{n}
>>

interactive bind_tl_wf {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- n > 0 -->
   "wf" : <H> >- l in BindTriangle{n -@ 1} -->
   "wf" : <H> >- length{l} > 0 -->
   <H> >- tl{l} in BindTriangle{n}
>>

interactive bind_triangle_elim {| elim |} 'H : <:xrule<
   "wf" : <H>; l: BindTriangle{n}; <J[l]> >- n in nat -->
   "base" : <H>; l: BindTriangle{n}; <J[l]> >- C[ [] ] -->
   "step" : <H>; l: BindTriangle{n}; <J[l]>; m: nat; m >= n; u: Bind{m}; v: BindTriangle{m +@ 1}; C[v] >- C[u::v] -->
   <H>; l: BindTriangle{n}; <J[l]> >- C[l]
>>

interactive bind_triangle_elim2  'H : <:xrule<
   "base" : <H>; n: nat; l: BindTriangle{n}; <J[n; l]>; m: nat >- C[m; [] ] -->
   "step" : <H>; n: nat; l: BindTriangle{n}; <J[n; l]>; m: nat; m >= n; u: Bind{m}; v: BindTriangle{m +@ 1}; C[m +@ 1; v] >- C[m; u::v] -->
   <H>; n: nat; l: BindTriangle{n}; <J[n; l]> >- C[n; l]
>>

(************************************************************************
 * Vector bindings.
 *)
doc <:doc<
   Vector bindings.
>>
interactive_rw reduce_bindn_vbind_up :
   bind{length{vlist{| <J> |}} +@ 1; l. 't['l]}
   <-->
   bind{v. bind{length{vlist{| <J> |}}; l. 't['v :: 'l]}}

interactive_rw vbind_eta_expand : <:xrewrite<
   vbind{| <J> >- e |}
   <-->
   bind{length{vlist{| <J> |}}; x. substl{vbind{| <J> >- e |}; x}}
>>

interactive_rw vbind_eta_reduce : <:xrewrite<
   bind{length{vlist{| <J> |}}; x. substl{vbind{| <J> >- e |}; x}}
   <-->
   vbind{| <J> >- e |}
>>

interactive vbind_in_bind {| intro |} : <:xrule<
   <H> >- vbind{| <J> >- e1 |} in Bind{length{vlist{| <J> |}}}
>>

interactive vbind_in_bind2 {| intro |} : <:xrule<
   <H> >- n = length{vlist{| <J> |}} in int -->
   <H> >- vbind{| <J> >- e1 |} in Bind{n}
>>

doc <:doc<
   Sometimes it is useful to use the depth of a term (usually this
   is during induction).
>>
interactive_rw reduce_bdepth_of_vbind {| reduce |} : <:xrewrite<
    bdepth{vbind{| <J> >- mk_terms{e} |}}
    <-->
    length{vlist{| <J> |}}
>>

(************************************************************************
 * Depth theorems
 *)
doc <:doc<
   More depth theorems.
>>
define unfold_probe : probe{'n; 't} <--> <:xterm<
   (fix probe i t ->
       if beq_int{i; 0} then
          "true"
       else
          "weak_dest_terms"{t;
             probe (i -@ 1) subst{t; mk_terms{it}};
             core. "false"}) n t
>>

interactive_rw reduce_probe : probe{'i; 't} <--> <:xterm<
   if beq_int{i; 0} then
      "true"
   else
      "weak_dest_terms"{t;
         probe{i -@ 1; subst{t; mk_terms{it}}};
         core. "false"}
>>

interactive_rw reduce_probe_zero {| reduce |} : <:xrewrite<
   probe{0; t}
   <-->
   "true"
>>

interactive_rw reduce_probe_succ_bind {| reduce |} : <:xrewrite<
   i in nat -->
   probe{i +@ 1; bind{x. e[x]}}
   <-->
   probe{i; e[mk_terms{it}]}
>>

interactive_rw reduce_probe_succ_mk_terms {| reduce |} : <:xrewrite<
   i in nat -->
   probe{i +@ 1; mk_terms{e}}
   <-->
   "false"
>>

interactive_rw reduce_probe_succ_mk_term {| reduce |} : <:xrewrite<
   i in nat -->
   probe{i +@ 1; mk_term{op; subterms}}
   <-->
   "false"
>>

interactive_rw reduce_probe_succ_var {| reduce |} : <:xrewrite<
   i in nat -->
   l in nat -->
   r in nat -->
   probe{i +@ 1; var{l; r}}
   <-->
   if beq_int{l; 0} then
      probe{i; bind{r; x. mk_terms{it}}}
   else
      probe{i; var{l -@ 1; r}}
>>

interactive_rw reduce_probe_succ_mk_bterm {| reduce |} : <:xrewrite<
   i in nat -->
   d in nat -->
   probe{i +@ 1; mk_bterm{d; op; subterms}}
   <-->
   if beq_int{d; 0} then
      "false"
   else
      probe{i; mk_bterm{d -@ 1; op; map{t. subst{t; mk_terms{it}}; subterms}}}
>>

interactive_rw reduce_probe_bindn : <:xrule<
   i in nat -->
   n in nat -->
   i <= n -->
   probe{i; bind{n; x. e[x]}}
   <-->
   "true"
>>

interactive_rw reduce_probe_bindn_mk_terms {| reduce |} : <:xrule<
   i in nat -->
   n in nat -->
   probe{i; bind{n; x. mk_terms{e[x]}}}
   <-->
   if le_bool{i; n} then
      "true"
   else
      "false"
>>

interactive_rw reduce_bterm_probe : <:xrule<
   e in BTerm -->
   n in nat -->
   probe{n; e}
   <-->
   if le_bool{n; bdepth{e}} then
      "true"
   else
      "false"
>>

interactive bterm_bind_depth : <:xrewrite<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- e in BTerm -->
   "wf" : <H> >- e in Bind{n} -->
   <H> >- bdepth{e} >= n
>>

(************************************************************************
 * Additional theorems.
 *)
doc <:doc<
   Reformulate some of the standard theorems in @tt[Itt_hoas_bterm].
>>
interactive subterms_bind_list1 'shape : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- shape in list{nat} -->
   "wf" : <H> >- subterms in list{BTerm} -->
   <H> >- compatible_shapes{n; shape; subterms} -->
   <H> >- subterms in list{Bind{n}}
>>

(************************************************************************
 * Tactics.
 *)
let relaxT = withOptionT relax_term "allow"

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
