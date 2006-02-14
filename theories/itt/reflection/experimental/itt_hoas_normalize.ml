doc <:doc<
   @module[Itt_hoas_normalize]x

   The @tt[Itt_hoas_normalize] module defines a normalization procedure
   for BTerms.

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
extends Itt_hoas_lof
extends Itt_hoas_lof_vec
extends Itt_vec_list1

doc docoff

open Lm_printf
open Basic_tactics
open Itt_hoas_base
open Itt_hoas_lof
open Itt_hoas_lof_vec
open Itt_hoas_vbind
open Itt_hoas_vector
open Itt_hoas_util
open Itt_hoas_debruijn

(************************************************************************
 * Common cases.
 *)
doc <:doc<
   Prove some common cases of normalization rules just so normalization
   is faster.  The tactic will work in all cases, so we can just catch the
   common ones.

   @docoff
>>
let extract_data tbl =
   let rw t =
      (* Find and apply the right tactic *)
      match Term_match_table.lookup tbl select_all t with
         Some conv -> conv
       | None -> raise (RefineError ("Itt_hoas_normalize.extract_data", StringTermError ("no reduction for", t)))
   in
      termC rw

(*
 * Pre-normalization.
 *)
let process_pre_normalize_simple_resource_rw_annotation = arith_rw_annotation "pre_normalize_simple"

let resource (term * conv, conv) pre_normalize_simple =
   table_resource_info extract_data

let preNormalizeSimpleTopC_env e =
   get_resource_arg (env_arg e) get_pre_normalize_simple_resource

let preNormalizeSimpleTopC = funC preNormalizeSimpleTopC_env

let preNormalizeSimpleC =
   funC (fun e -> sweepUpC (preNormalizeSimpleTopC_env e))

let preNormalizeSimpleT =
   rwAll preNormalizeSimpleC

(*
 * Simple normalizer.
 *)
let process_normalize_simple_resource_rw_annotation = arith_rw_annotation "normalize_simple"

let resource (term * conv, conv) normalize_simple =
   table_resource_info extract_data

let normalizeSimpleTopC_env e =
   get_resource_arg (env_arg e) get_normalize_simple_resource

let normalizeSimpleTopC = funC normalizeSimpleTopC_env

let normalizeSimpleC =
   funC (fun e -> sweepDnC (repeatC (normalizeSimpleTopC_env e)))

let normalizeSimpleT =
   rwAll normalizeSimpleC

doc <:doc<
   Pre-normalization.  This eliminates the non-canonical forms.
>>
let resource pre_normalize_simple +=
   [<< mk_term{'op; 'subterms} >>, fold_mk_term;
    << subst{'e1; 'e2} >>, subst_to_substl;
    << bind{x. 'e['x]} >>, bind_into_bindone]

doc <:doc<
   Now we have a series of simple normalization theorems.
   The following or for pushing @tt[bindn] through @tt[mk_bterm].
>>
interactive_rw bindn_of_mk_bterm0 {| normalize_simple |} : <:xrewrite<
   n in nat -->
   m in nat -->
   bind{n; x. mk_bterm{m; op; []}}
   <-->
   mk_bterm{m +@ n; op; []}
>>

interactive_rw bindn_of_mk_bterm1 {| normalize_simple |} : <:xrewrite<
   n in nat -->
   m in nat -->
   bind{n; x. mk_bterm{m; op; [e1[x]]}}
   <-->
   mk_bterm{m +@ n; op; [bind{n; x. e1[x]}]}
>>

interactive_rw bindn_of_mk_bterm2 {| normalize_simple |} : <:xrewrite<
   n in nat -->
   m in nat -->
   bind{n; x. mk_bterm{m; op; [e1[x]; e2[x]]}}
   <-->
   mk_bterm{m +@ n; op; [bind{n; x. e1[x]}; bind{n; x. e2[x]}]}
>>

interactive_rw bindn_of_mk_bterm3 {| normalize_simple |} : <:xrewrite<
   n in nat -->
   m in nat -->
   bind{n; x. mk_bterm{m; op; [e1[x]; e2[x]; e3[x]]}}
   <-->
   mk_bterm{m +@ n; op; [bind{n; x. e1[x]}; bind{n; x. e2[x]}; bind{n; x. e3[x]}]}
>>

interactive_rw bindn_of_mk_bterm4 {| normalize_simple |} : <:xrewrite<
   n in nat -->
   m in nat -->
   bind{n; x. mk_bterm{m; op; [e1[x]; e2[x]; e3[x]; e4[x]]}}
   <-->
   mk_bterm{m +@ n; op; [bind{n; x. e1[x]}; bind{n; x. e2[x]}; bind{n; x. e3[x]}; bind{n; x. e4[x]}]}
>>

interactive_rw bindn_of_mk_bterm5 {| normalize_simple |} : <:xrewrite<
   n in nat -->
   m in nat -->
   bind{n; x. mk_bterm{m; op; [e1[x]; e2[x]; e3[x]; e4[x]; e5[x]]}}
   <-->
   mk_bterm{m +@ n; op; [bind{n; x. e1[x]}; bind{n; x. e2[x]}; bind{n; x. e3[x]}; bind{n; x. e4[x]}; bind{n; x. e5[x]}]}
>>

doc <:doc<
   A similar set of theorems for << vbind{| <J> >- 'e |} >>.
>>
interactive_rw vbind_of_mk_bterm0 {| normalize_simple |} : <:xrewrite<
   n in nat -->
   vbind{| <J> >- mk_bterm{n<||>; op<||>; []} |}
   <-->
   mk_bterm{n +@ length{vlist{| <J> |}}; op; []}
>>

interactive_rw vbind_of_mk_bterm1 {| normalize_simple |} : <:xrewrite<
   n in nat -->
   vbind{| <J> >- mk_bterm{n<||>; op<||>; [e1]} |}
   <-->
   mk_bterm{n +@ length{vlist{| <J> |}}; op; [vbind{| <J> >- e1 |}]}
>>

interactive_rw vbind_of_mk_bterm2 {| normalize_simple |} : <:xrewrite<
   n in nat -->
   vbind{| <J> >- mk_bterm{n<||>; op<||>; [e1; e2]} |}
   <-->
   mk_bterm{n +@ length{vlist{| <J> |}}; op; [vbind{| <J> >- e1 |}; vbind{| <J> >- e2 |}]}
>>

interactive_rw vbind_of_mk_bterm3 {| normalize_simple |} : <:xrewrite<
   n in nat -->
   vbind{| <J> >- mk_bterm{n<||>; op<||>; [e1; e2; e3]} |}
   <-->
   mk_bterm{n +@ length{vlist{| <J> |}}; op; [vbind{| <J> >- e1 |}; vbind{| <J> >- e2 |}; vbind{| <J> >- e3 |}]}
>>

interactive_rw vbind_of_mk_bterm4 {| normalize_simple |} : <:xrewrite<
   n in nat -->
   vbind{| <J> >- mk_bterm{n<||>; op<||>; [e1; e2; e3; e4]} |}
   <-->
   mk_bterm{n +@ length{vlist{| <J> |}}; op; [vbind{| <J> >- e1 |};
                                              vbind{| <J> >- e2 |};
                                              vbind{| <J> >- e3 |};
                                              vbind{| <J> >- e4 |}]}
>>

interactive_rw vbind_of_mk_bterm5 {| normalize_simple |} : <:xrewrite<
   n in nat -->
   vbind{| <J> >- mk_bterm{n<||>; op<||>; [e1; e2; e3; e4; e5]} |}
   <-->
   mk_bterm{n +@ length{vlist{| <J> |}}; op; [vbind{| <J> >- e1 |};
                                              vbind{| <J> >- e2 |};
                                              vbind{| <J> >- e3 |};
                                              vbind{| <J> >- e4 |};
                                              vbind{| <J> >- e5 |}]}
>>

doc <:doc<
   Optimizations.
>>
interactive_rw substl_merge1 {| normalize_simple |} : <:xrewrite<
   m in nat -->
   bind{m +@ 1; x. substl{substl{e; nth_prefix{x; m}}; [hd{nth_suffix{x; m}}]}}
   <-->
   bind{m +@ 1; x. substl{e; x}}
>>

doc <:doc<
   We also perform coalescing during normalization.
>>
let resource normalize_simple +=
   [<< bind{'n; x. bind{'m; y. 'e['x; 'y]}} >>, coalesce_bindn_bindn]

interactive_rw coalesce_vbind_bind1 {| normalize_simple |} : <:xrewrite<
   vbind{| <J> >- bind{1; x. e[x]} |}
   <-->
   vbind{| <J>; x: it >- e[ [x] ] |}
>>

(************************************************************************
 * Tactics.
 *)
doc <:doc<
   The ``simple'' normalizer works with a pre-defined set of theorems
   for a finite number of different shapes.  Also, it does not perform
   any kind of optimization.  These are the steps:

   @begin[enumerate]
   @item{{Eliminate all << mk_term{'op; 'subterms} >>.}}
   @item{{Eliminate all << bind{x. 'e['x]} >>.}}
   @item{{Coalesce binds.}}
   @item{{Push binds down using the finite database.}}
   @end[enumerate]

   The simple normalizer will fail on terms that are not already part
   of the finite database (for example, on terms with a lot of
   subterms, for which we haven't proved the theorems).  In this
   case, it is necessary to fall back to the general normalizer
   @tt[normalizeBTermC] below.
>>
let normalizeBTermSimpleC_inner =
   preNormalizeSimpleC
   thenC normalizeSimpleC

doc <:doc<
   The normalization conversion performs the following steps:

   @begin[enumerate]
   @item{{Eliminate all << mk_term{'op; 'subterms} >>.}}
   @item{{Eliminate all << bind{x. 'e['x]} >>.}}
   @item{{Coalesce binds.}}
   @item{{Push binds down.}}
   @item{{Coalesce substitutions.}}
   @end[enumerate]

   The @tt[preNormalizeLofC] conversion performs the first two steps.
   The @tt[reduceLofC] conversion coalesces binds and pushes them down.
   The @tt[reduceLofC] conversion must be run with all @tt[lof] terms
   hoisted as much as possible---it should be run after @tt[normalizeLofC].
   The @tt[normalizeLofC] convertion pushed hoists the lof terms as much as possible
   and coalesces substl terms.
   @docoff
>>
let normalizeBTermAuxC =
   preNormalizeLofC
   thenC normalizeLofC
   thenC reduceLofC

doc <:doc<
   Once the binds have all been pushed, use the @tt[reduceC] conversion
   to optimize the term.  Afterwards, remove all temporary terms using the
   @tt[lofBindElimC] conversion.
>>
let normalizeBTermForceC_inner =
   normalizeBTermAuxC
   thenC reduceC
   thenC sweepUpC lofBindElimC
   thenC sweepUpC lofVBindElimC

doc <:doc<
   For normalization, use the simple normalizer first.
   Then use the generalized normalizer.
>>
let normalizeBTermC_inner =
   normalizeBTermSimpleC_inner
   thenC tryC (progressC normalizeBTermForceC_inner)

doc <:doc<
   The normalizers will often be used on equality goals.
   To reduce the amount of work, convert the equality to a membership
   if possible, and reduce a single term instead of two identical ones.
>>
define unfold_member : member{'T; 'e} <--> 'e = 'e in 'T

let fold_member = makeFoldC << member{'T; 'e} >> unfold_member

let memberC c =
   tryC fold_member
   thenC c
   thenC tryC unfold_member

let normalizeBTermForceC =
   memberC normalizeBTermForceC_inner

let normalizeBTermSimpleC =
   normalizeBTermSimpleC_inner

let normalizeBTermC =
   memberC normalizeBTermC_inner

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
