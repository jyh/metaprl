doc <:doc<
   @module[Itt_hoas_lof]

   During normalization, we define a custom version of list_of_fun,
   called << lof{i. 'f['i]; 'n} >>.  The expressions << 'f['i] >> are
   stylizied, and include only operations that correspond directly
   to list operations.  The style is designed carefully to make the
   conversion reversible.  Normal lists can be converted to @tt[lof]
   and back without change.

   @docoff

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2005-2006 MetaPRL Group, Caltech

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
extends Itt_list3
extends Itt_hoas_debruijn

doc docoff

open Lm_printf
open Basic_tactics
open Simple_print
open Itt_hoas_vector
open Itt_hoas_debruijn
open Itt_hoas_util

(************************************************************************
 * Resources.
 *)
doc <:doc<
   The << lof{i. 'f['i]; 'n} >> normalizers follow the same pattern as in Itt_list3.

   Invariant: the @tt[normalize_lof] tactic works using @tt[sweepUpC] and
   @tt[reduce_lof] works using @tt[sweepDnC].  When choosing which resource
   to use, do not break the direction of operation.

   @docoff
>>
let extract_data tbl =
   let rw t =
      let conv =
         try
            (* Find and apply the right tactic *)
            Term_match_table.lookup tbl select_all t
         with
            Not_found ->
               raise (RefineError ("Conversionals.extract_data", StringTermError ("no reduction for", t)))
      in
         conv
   in
      termC rw

(*
 * Normalizing resource (lof lifting).
 *)
let process_pre_normalize_lof_resource_rw_annotation = arith_rw_annotation "pre_normalize_lof"

let resource (term * conv, conv) pre_normalize_lof =
   table_resource_info extract_data

let preNormalizeLofTopC_env e =
   get_resource_arg (env_arg e) get_pre_normalize_lof_resource

let preNormalizeLofTopC = funC preNormalizeLofTopC_env

let preNormalizeLofC =
   funC (fun e -> sweepUpC (preNormalizeLofTopC_env e))

let preNormalizeLofT =
   rwAll preNormalizeLofC

(*
 * Normalizing resource (lof lifting).
 *)
let process_normalize_lof_resource_rw_annotation = arith_rw_annotation "normalize_lof"

let resource (term * conv, conv) normalize_lof =
   table_resource_info extract_data

let normalizeLofTopC_env e =
   get_resource_arg (env_arg e) get_normalize_lof_resource

let normalizeLofTopC = funC normalizeLofTopC_env

let normalizeLofC =
   funC (fun e -> sweepUpC (normalizeLofTopC_env e))

let normalizeLofT =
   rwAll normalizeLofC

(*
 * Reduce resource (lof lowering).
 *)
let process_reduce_lof_resource_rw_annotation = arith_rw_annotation "reduce_lof"

let resource (term * conv, conv) reduce_lof =
   table_resource_info extract_data

let reduceLofTopC_env e =
   get_resource_arg (env_arg e) get_reduce_lof_resource

let reduceLofTopC = funC reduceLofTopC_env

let reduceLofC =
   funC (fun e -> sweepDnC (repeatC (reduceLofTopC_env e)))

let reduceLofT =
   rwAll reduceLofC

(************************************************************************
 * Normalization for list_of_fun.
 *)
doc <:doc<
   We use << list_of_fun{i. 'f['i]; 'n} >> to normalize nested substitutions.
   We define a stylized version << lof{i. 'f['i]; 'n} >> to make the work easier.
>>
define unfold_lof : lof{i. 'f['i]; 'n} <-->
   list_of_fun{i. 'f['i]; 'n}

define unfold_lof_bind : lof_bind{'n; x. 'e['x]} <-->
   bind{'n; x. 'e['x]}

doc <:doc<
   In the stylized version << lof{i. 'f['i]; 'n} >>, define some expressions
   for << 'f['i] >>.
>>
define unfold_lof_nth : lof_nth{'x; 'i} <-->
   nth{'x; 'i}

define unfold_lof_nil : lof_nil <-->
   it

define unfold_lof_tl : lof_tl{i. 'f['i]; 'i} <-->
   'f['i +@ 1]

define unfold_lof_cons : lof_cons{i. 'f['i]; 'i; 'e} <-->
   if beq_int{'i; 0} then
      'e
   else
      'f['i -@ 1]

define unfold_lof_nth_prefix : lof_nth_prefix{i. 'f['i]; 'i; 'n; 'm} <-->
   'f['i]

define unfold_lof_nth_suffix : lof_nth_suffix{i. 'f['i]; 'i; 'n; 'm} <-->
   'f['i +@ 'm]

define unfold_lof_append : lof_append{i. 'f['i]; j. 'g['j]; 'i; 'n; 'm} <-->
   if lt_bool{'i; 'n} then
      'f['i]
   else
      'g['i -@ 'n]

(************************************************************************
 * Term functions.
 *)
let lof_term = << lof{i. 'f['i]; 'n} >>
let lof_opname = opname_of_term lof_term
let is_lof_term = is_dep1_dep0_term lof_opname
let mk_lof_term = mk_dep1_dep0_term lof_opname
let dest_lof_term = dest_dep1_dep0_term lof_opname

let lof_bind_term = << lof_bind{'n; x. 'e['x]} >>
let lof_bind_opname = opname_of_term lof_bind_term
let is_lof_bind_term = is_dep0_dep1_term lof_bind_opname
let dest_lof_bind_term = dest_dep0_dep1_term lof_bind_opname
let mk_lof_bind_term = mk_dep0_dep1_term lof_bind_opname

let fold_lof_bind = makeFoldC << lof_bind{'n; x. 'e['x]} >> unfold_lof_bind

let var_i = Lm_symbol.add "i"
let var_z = Lm_symbol.add "z"

(************************************************************************
 * Some standard rules.
 *)
interactive lof_id {| intro [] |} :
   sequent { <H> >- 'n1 = 'n2 in nat } -->
   sequent { <H>; k: nat; 'k < 'n1 >- 'f1['k] ~ 'f2['k] } -->
   sequent { <H> >- lof{k. 'f1['k]; 'n1} ~ lof{k. 'f2['k]; 'n2} }

interactive lof_wf2 {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- lof{i. 'f['i]; 'n} in list }

(************************************************************************
 * Normalization rules.
 *)
doc <:doc<
   Normalization rules.
>>
interactive_rw nil_lof {| normalize_lof |} :
   nil
   <-->
   lof{i. lof_nil; 0}

interactive_rw nth_prefix_lof {| normalize_lof |} :
   'n in nat -->
   'm in nat -->
   'm <= 'n -->
   nth_prefix{lof{i. 'f['i]; 'n}; 'm}
   <-->
   lof{i. lof_nth_prefix{i. 'f['i]; 'i; 'n; 'm}; 'm}

interactive_rw nth_suffix_lof {| normalize_lof |} :
   'n in nat -->
   'm in nat -->
   'm <= 'n -->
   nth_suffix{lof{i. 'f['i]; 'n}; 'm}
   <-->
   lof{i. lof_nth_suffix{i. 'f['i]; 'i; 'n; 'm}; 'n -@ 'm}

interactive_rw tl_lof {| normalize_lof |} :
   'n in nat -->
   'n > 0 -->
   tl{lof{i. 'f['i]; 'n}}
   <-->
   lof{i. lof_tl{i. 'f['i]; 'i}; 'n -@ 1}

interactive_rw cons_lof {| normalize_lof |} :
   'n in nat -->
   cons{'e; lof{i. 'f['i]; 'n}}
   <-->
   lof{i. lof_cons{i. 'f['i]; 'i; 'e}; 'n +@ 1}

interactive_rw append_lof {| normalize_lof |} :
   'm in nat -->
   'n in nat -->
   append{lof{k. 'f['k]; 'm}; lof{k. 'g['k]; 'n}}
   <-->
   lof{i. lof_append{i. 'f['i]; i. 'g['i]; 'i; 'm; 'n}; 'm +@ 'n}

(************************************************************************
 * Reductions.
 *)
doc <:doc<
   Once a normalization has happened, we may want to convert back to the
   original list form.  The following rewrites reverse the
   normalization.
>>
interactive_rw reduce_nil_lof {| reduce_lof |} :
   lof{i. lof_nil; 0}
   <-->
   nil

interactive_rw reduce_nth_prefix_lof {| reduce_lof |} :
   'n in nat -->
   'm <= 'n -->
   'p = 'm in nat -->
   lof{i. lof_nth_prefix{i. 'f['i]; 'i; 'n; 'm}; 'p}
   <-->
   nth_prefix{lof{i. 'f['i]; 'n}; 'm}

interactive_rw reduce_nth_suffix_lof {| reduce_lof |} :
   'n in nat -->
   'm in nat -->
   'm <= 'n -->
   'p = 'n -@ 'm in nat -->
   lof{i. lof_nth_suffix{i. 'f['i]; 'i; 'n; 'm}; 'p}
   <-->
   nth_suffix{lof{i. 'f['i]; 'n}; 'm}

interactive_rw reduce_tl_lof {| reduce_lof |} :
   'n in nat -->
   lof{i. lof_tl{i. 'f['i]; 'i}; 'n}
   <-->
   tl{lof{i. 'f['i]; 'n +@ 1}}

interactive_rw reduce_cons_lof {| reduce_lof |} :
   'n in nat -->
   'n > 0 -->
   lof{i. lof_cons{i. 'f['i]; 'i; 'e}; 'n}
   <-->
   cons{'e; lof{i. 'f['i]; 'n -@ 1}}

interactive_rw reduce_append_lof {| reduce_lof |} :
   'm in nat -->
   'n in nat -->
   'p = 'm +@ 'n in nat -->
   lof{i. lof_append{i. 'f['i]; i. 'g['i]; 'i; 'm; 'n}; 'p}
   <-->
   append{lof{k. 'f['k]; 'm}; lof{k. 'g['k]; 'n}}

(************************************************************************
 * Bind-pushing.
 *)
doc <:doc<
   Binds migrate inwards during reduction.
>>
interactive_rw lof_bind_nil {| reduce_lof |} :
   lof{j. lof_bind{'n; x. lof_nil}; 0}
   <-->
   lof{j. lof_nil; 0}

interactive_rw lof_bind_cons {| reduce_lof |} :
   'm in nat -->
   lof{j. lof_bind{'n; x. lof_cons{i. 'f['i; 'x]; 'j; 'e['x]}}; 'm}
   <-->
   lof{j. lof_cons{i. lof_bind{'n; x. 'f['i; 'x]}; 'j; lof_bind{'n; x. 'e['x]}}; 'm}

interactive_rw lof_bind_tl {| reduce_lof |} :
   lof{j. lof_bind{'n; x. lof_tl{i. 'f['i; 'x]; 'j}}; 'm}
   <-->
   lof{j. lof_tl{i. lof_bind{'n; x. 'f['i; 'x]}; 'j}; 'm}

interactive_rw lof_bind_nth_prefix {| reduce_lof |} :
   'r in nat -->
   lof{j. lof_bind{'n; x. lof_nth_prefix{i. 'f['i; 'x]; 'j; 'p; 'q}}; 'r}
   <-->
   lof{j. lof_nth_prefix{i. lof_bind{'n; x. 'f['i; 'x]}; 'j; 'p; 'q}; 'r}

interactive_rw lof_bind_nth_suffix {| reduce_lof |} :
   'r in nat -->
   lof{j. lof_bind{'n; x. lof_nth_suffix{i. 'f['i; 'x]; 'j; 'p; 'q}}; 'r}
   <-->
   lof{j. lof_nth_suffix{i. lof_bind{'n; x. 'f['i; 'x]}; 'j; 'p; 'q}; 'r}

interactive_rw lof_bind_append {| reduce_lof |} :
   'r in nat -->
   'p in nat -->
   lof{j. lof_bind{'n; x. lof_append{i. 'f['i; 'x]; k. 'g['k; 'x]; 'j; 'p; 'q}}; 'r}
   <-->
   lof{j. lof_append{i. lof_bind{'n; x. 'f['i; 'x]}; k. lof_bind{'n; x. 'g['k; 'x]}; 'j; 'p; 'q}; 'r}

(************************************************************************
 * Bind forms.
 *)
doc <:doc<
   Convert the expression in a << bind{'n; x. 'e['x]} >> to lof form.
>>
let resource pre_normalize_lof +=
   [<< mk_term{'op; 'subterms} >>, fold_mk_term;
    << subst{'e1; 'e2} >>, subst_to_substl]

interactive_rw bindn_to_lof_bind {| pre_normalize_lof |} :
   'n in nat -->
   bind{'n; x. 'e['x]}
   <-->
   lof_bind{'n; x. 'e[lof{i. lof_nth{'x; 'i}; 'n}]}

interactive_rw bind_to_lof_bind {| pre_normalize_lof |} :
   bind{x. 'e['x]}
   <-->
   lof_bind{1; x. 'e[hd{'x}]}

interactive_rw coalesce_lof_bind :
   'n in nat -->
   'm in nat -->
   lof_bind{'n; x. lof_bind{'m; y. 'e['x; 'y]}}
   <-->
   lof_bind{'n +@ 'm; x. 'e[nth_prefix{lof{i. lof_nth{'x; 'i}; 'n +@ 'm}; 'n};
                            nth_suffix{lof{i. lof_nth{'x; 'i}; 'n +@ 'm}; 'n}]}

interactive_rw substl_substl_lof2 :
   'n in nat -->
   'm in nat -->
   substl{substl{'e; lof{x. 'f['x]; 'm}}; lof{x. 'g['x]; 'n}}
   <-->
   substl{'e; lof{i. lof_append{i. 'f['i]; i. 'g['i]; 'i; 'm; 'n}; 'm +@ 'n}}

(************************************************************************
 * Standard facts.
 *)
interactive_rw lof_bind_zero {| reduce |} :
   lof_bind{0; x. 'e['x]}
   <-->
   'e[nil]

interactive_rw lof_bind_succ :
   'n in nat -->
   lof_bind{'n +@ 1; x. 'e['x]}
   <-->
   bind{y. lof_bind{'n; x. 'e['y :: 'x]}}

interactive_rw reduce_lof_bind_right :
   'n in nat -->
   lof_bind{'n +@ 1; x. 'e['x]}
   <-->
   lof_bind{'n; x. bind{y. 'e[append{'x; cons{'y; nil}}]}}

interactive_rw reduce_lof_bind_mk_bterm {| reduce_lof |} :
   'i in nat -->
   'n in nat -->
   'm in nat -->
   lof_bind{'i; x. mk_bterm{'n; 'op; lof{y. 'f['x; 'y]; 'm}}}
   <-->
   mk_bterm{'n +@ 'i; 'op; lof{y. lof_bind{'i; x. 'f['x; 'y]}; 'm}}

(************************************************************************
 * Lof removal.
 *)
doc <:doc<
   After a reduction, remove as many lof as possible.
>>
interactive_rw lof_lof_elim :
   'n in nat -->
   lof{i. lof_nth{lof{j. 'f['j]; 'n}; 'i}; 'n}
   <-->
   lof{i. 'f['i]; 'n}

interactive_rw lof_bind_elim Perv!bind{x, z. 'e['x; 'z]} :
   'n in nat -->
   lof_bind{'n; x. 'e['x; lof{i. lof_nth{'x; 'i}; 'n}]}
   <-->
   bind{'n; x. 'e['x; 'x]}

doc docoff

let lof_bind_elim_conv t =
   if is_lof_bind_term t then
      let x, n, e = dest_lof_bind_term t in
      let fv = all_vars e in
      let i = maybe_new_var_set var_i fv in
      let z = maybe_new_var_set var_z fv in
      let lof = <:con< lof{$i$. lof_nth{$mk_var_term x$; $mk_var_term i$}; $n$} >> in
      let t_bind = mk_bind2_term x z (var_subst e lof z) in
         lof_bind_elim t_bind
   else
      raise (RefineError ("lof_bind_elim", StringTermError ("not a lof_bind term", t)))

let lofBindElimC = termC lof_bind_elim_conv

(*
 * During bind coalescing, eliminate the lof first, then coalesce,
 * then re-introduce it.
 *)
let coalesce_bind t =
   (* Check terms to make this faster *)
   let _, _, s = dest_lof_bind_term t in
      if is_lof_bind_term s then
         lofBindElimC
         thenC addrC [Subterm 2] lofBindElimC
         thenC coalesce_bindn_bindn thenC addrC [Subterm 1] reduceC
         thenC bindn_to_lof_bind
      else
         raise (RefineError ("coalesce_bind", StringTermError ("not a nested bind", t)))

let coalesce_bindC = termC coalesce_bind

let resource reduce_lof +=
   [<< lof_bind{'n; x. lof_bind{'m; y. 'e['x; 'y]}} >>, coalesce_bindC]

(************************************************************************
 * Constant reductions.
 *)
doc <:doc<
   Constant reductions.
>>
interactive_rw hd_lof {| reduce; reduce_lof |} :
   'n in nat -->
   'n > 0 -->
   hd{lof{i. 'f['i]; 'n}}
   <-->
   'f[0]

interactive_rw reduce_nth_lof {| reduce; reduce_lof |} :
   'n in nat -->
   'j in nat -->
   'j < 'n -->
   lof_nth{lof{i. 'f['i]; 'n}; 'j}
   <-->
   'f['j]

interactive_rw reduce_singleton {| normalize_lof; reduce; reduce_lof |} : <:xrewrite<
   lof_cons{i. f[i]; 0; e}
   <-->
   e
>>

doc docoff

let resource reduce_lof +=
   << lof_nth_suffix{i. 'f['i]; number[n:n]; 'n; 'm} >>, unfold_lof_nth_suffix

let resource reduce +=
   << lof_nth_suffix{i. 'f['i]; number[n:n]; 'n; 'm} >>, wrap_reduce unfold_lof_nth_suffix

let resource normalize_lof += [
   << lof_nth_suffix{i. 'f['i]; number[n:n]; 'n; 'm} >>, (unfold_lof_nth_suffix thenC reduceC);
   << hd{lof{i. 'f['i]; 'n}} >>, (hd_lof thenC reduceC);
   << lof_nth{lof{i. 'f['i]; 'n}; 'j} >>, (reduce_nth_lof thenC reduceC)
]

(************************************************************************
 * Optimizations.
 * XXX: Aleksey: it is not clear whether this is needed at all.
 *)
doc <:doc<
   Optimizations.
>>
interactive_rw reduce_append_prefix_singleton {| reduce_lof |} :
   'n2 = 'n3 in nat -->
   'n5 in nat -->
   'n3 = 'n5 -@ 1 in nat -->
   lof{i. lof_append{j1. lof_nth_prefix{j2. lof_nth{'x; 'j2}; 'j1; 'n1; 'n2};
                     j2. lof_cons{j3. lof_nil; 'j2; lof_nth{'x; 'n2}};
                     'i; 'n3; 'n4}; 'n5}
   <-->
   lof{i. lof_nth{'x; 'i}; 'n5}

(************************************************************************
 * Add substl coalescing to normalize_lof
 *)
let resource normalize_lof +=
    << substl{substl{'e; lof{x. 'f['x]; 'm}}; lof{x. 'g['x]; 'n}} >>,
    (substl_substl_lof2
     thenC addrC [Subterm 2; Subterm 2] reduceC
     thenC addrC [Subterm 2] (tryC reduce_append_prefix_singleton))

(************************************************************************
 * Display forms.
 *)
dform lof_df : lof{i. 'f; 'n} =
   szone pushm[3] `"LOF(" 'i `" -> " slot{'f} `";" hspace slot{'n} `")" popm ezone

dform lof_nil_df : lof_nil =
   `"NIL"

dform lof_cons_df : lof_cons{i. 'f; 'j; 'e} =
   szone pushm[3] `"CONS(" 'i `" -> " slot{'f} `";" hspace slot{'j} `";" hspace slot{'e} `")" popm ezone

dform lof_nth_df : lof_nth{'f; 'i} =
   szone pushm[3] `"NTH(" slot{'f} `";" hspace slot{'i} `")" popm ezone

dform lof_nth_prefix_df : lof_nth_prefix{i. 'f; 'j; 'n; 'm} =
   szone pushm[3] `"PREFIX(" 'i `" -> " slot{'f} `";" hspace slot{'j} `";" hspace slot{'n} `";" hspace slot{'m} `")" popm ezone

dform lof_nth_prefix_df : lof_nth_suffix{i. 'f; 'j; 'n; 'm} =
   szone pushm[3] `"SUFFIX(" 'i `" -> " slot{'f} `";" hspace slot{'j} `";" hspace slot{'n} `";" hspace slot{'m} `")" popm ezone

dform lof_append_df : lof_append{i. 'f; j. 'g; 'k; 'n; 'm} =
   szone pushm[3] `"APPEND(" 'i `" -> " slot{'f} `";" hspace
                             'j `" -> " slot{'g} `";" hspace
                             slot{'k} `";" hspace
                             slot{'n} `";" hspace
                             slot{'m} `")" popm ezone

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
