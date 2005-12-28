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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}

   @end[license]
   @parents
>>
extends Itt_list3
extends Itt_hoas_bterm

doc docoff

open Lm_printf
open Basic_tactics
open Simple_print
open Itt_hoas_vector

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
 * Resource.
 *)
let process_normalize_lof_resource_rw_annotation = redex_and_conv_of_rw_annotation "normalize_lof"

let resource (term * conv, conv) normalize_lof =
   table_resource_info extract_data

let normalizeLofTopC_env e =
   get_resource_arg (env_arg e) get_normalize_lof_resource

let normalizeLofTopC = funC normalizeLofTopC_env

let normalizeLofC =
   funC (fun e -> repeatC (sweepUpC (normalizeLofTopC_env e)))

let normalizeLofT =
   rwAll normalizeLofC

(*
 * Resource.
 *)
let process_reduce_lof_resource_rw_annotation = redex_and_conv_of_rw_annotation "reduce_lof"

let resource (term * conv, conv) reduce_lof =
   table_resource_info extract_data

let reduceLofTopC_env e =
   get_resource_arg (env_arg e) get_reduce_lof_resource

let reduceLofTopC = funC reduceLofTopC_env

let reduceLofC =
   funC (fun e -> repeatC (sweepDnC (reduceLofTopC_env e)))

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

interactive_rw hd_lof {| normalize_lof |} :
   'n in nat -->
   not{'n = 0 in nat} -->
   hd{lof{i. 'f['i]; 'n}}
   <-->
   'f[0]

interactive_rw tl_lof {| normalize_lof |} :
   'n in nat -->
   not{'n = 0 in nat} -->
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
   'n = 0 in nat -->
   lof{i. lof_nil; 'n}
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
   not{'n = 0 in nat} -->
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
   'm = 0 in nat -->
   lof{j. lof_bind{'n; x. lof_nil}; 'm}
   <-->
   lof{j. lof_nil; 'm}

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

doc <:doc<
   We also want to push binds inward in the normal form.
>>
interactive_rw push_lof_bind_nil Perv!bind{j, z. 'S['j; 'z]}
 Perv!bind{j. lof_bind{'n; x. lof_nil}} :
   'm = 0 in nat -->
   lof{j. 'S['j; lof_bind{'n; x. lof_nil}]; 'm}
   <-->
   lof{j. 'S['j; lof_nil]; 'm}

interactive_rw push_lof_bind_cons Perv!bind{j, z. 'S['j; 'z]}
 Perv!bind{j. lof_bind{'n; x. lof_cons{i. 'f['j; 'i; 'x]; 'j; 'e['j; 'x]}}} :
   'm in nat -->
   lof{j. 'S['j; lof_bind{'n; x. lof_cons{i. 'f['j; 'i; 'x]; 'j; 'e['j; 'x]}}]; 'm}
   <-->
   lof{j. 'S['j; lof_cons{i. lof_bind{'n; x. 'f['j; 'i; 'x]}; 'j; lof_bind{'n; x. 'e['j; 'x]}}]; 'm}

interactive_rw push_lof_bind_tl Perv!bind{j, z. 'S['j; 'z]}
 Perv!bind{j. lof_bind{'n; x. lof_tl{i. 'f['j; 'i; 'x]; 'j}}} :
   lof{j. 'S['j; lof_bind{'n; x. lof_tl{i. 'f['j; 'i; 'x]; 'j}}]; 'm}
   <-->
   lof{j. 'S['j; lof_tl{i. lof_bind{'n; x. 'f['j; 'i; 'x]}; 'j}]; 'm}

interactive_rw push_lof_bind_nth_prefix Perv!bind{j, z. 'S['j; 'z]}
 Perv!bind{j. lof_bind{'n; x. lof_nth_prefix{i. 'f['j; 'i; 'x]; 'j; 'p; 'q}}} :
   'r in nat -->
   lof{j. 'S['j; lof_bind{'n; x. lof_nth_prefix{i. 'f['j; 'i; 'x]; 'j; 'p; 'q}}]; 'r}
   <-->
   lof{j. 'S['j; lof_nth_prefix{i. lof_bind{'n; x. 'f['j; 'i; 'x]}; 'j; 'p; 'q}]; 'r}

interactive_rw push_lof_bind_nth_suffix Perv!bind{j, z. 'S['j; 'z]}
 Perv!bind{j. lof_bind{'n; x. lof_nth_suffix{i. 'f['j; 'i; 'x]; 'j; 'p; 'q}}} :
   'r in nat -->
   lof{j. 'S['j; lof_bind{'n; x. lof_nth_suffix{i. 'f['j; 'i; 'x]; 'j; 'p; 'q}}]; 'r}
   <-->
   lof{j. 'S['j; lof_nth_suffix{i. lof_bind{'n; x. 'f['j; 'i; 'x]}; 'j; 'p; 'q}]; 'r}

interactive_rw push_lof_bind_append Perv!bind{j, z. 'S['j; 'z]}
 Perv!bind{j. lof_bind{'n; x. lof_append{i. 'f['j; 'i; 'x]; k. 'g['j; 'k; 'x]; 'j; 'p; 'q}}} :
   'r in nat -->
   'p in nat -->
   lof{j. 'S['j; lof_bind{'n; x. lof_append{i. 'f['j; 'i; 'x]; k. 'g['j; 'k; 'x]; 'j; 'p; 'q}}]; 'r}
   <-->
   lof{j. 'S['j; lof_append{i. lof_bind{'n; x. 'f['j; 'i; 'x]}; k. lof_bind{'n; x. 'g['j; 'k; 'x]}; 'j; 'p; 'q}]; 'r}

doc docoff

(*
 * Standardizing.
 *)
let standardize_conv t =
   foldC (standardize t) idC

let standardizeC = termC standardize_conv

(*
 * Define a tactic to push the binds down through the lof term.
 *)
let subterm1_addr = make_address [Subterm 1]
let subterm2_addr = make_address [Subterm 2]
let subterm3_addr = make_address [Subterm 3]

let mk_subterm1_addr addr =
   compose_address addr subterm1_addr

let mk_subterm2_addr addr =
   compose_address addr subterm2_addr

let mk_subterm3_addr addr =
   compose_address addr subterm3_addr

let rec push_bind z addr t =
   if is_lof_term t then
      let j, t, _ = dest_lof_term t in
      let t_bind = term_subterm t addr in
         if is_lof_bind_term t_bind then
            let p_bind = mk_bind2_term j z (replace_subterm t addr (mk_var_term z)) in
            let _, _, s = dest_lof_bind_term t_bind in
            let t_bind = mk_bind1_term j t_bind in
               match explode_term s with
                  << lof_nil >> ->
                     push_lof_bind_nil p_bind t_bind
                | << lof_cons{i. 'f; 'j; 'e} >> ->
                     push_lof_bind_cons p_bind t_bind
(*
                     thenC termC (push_bind z (mk_subterm1_addr addr))
 *)
                     thenC termC (push_bind z (mk_subterm3_addr addr))
                | << lof_tl{i. 'f; 'j} >> ->
                     push_lof_bind_tl p_bind t_bind
                     thenC termC (push_bind z (mk_subterm1_addr addr))
                | << lof_nth_prefix{i. 'f; 'j; 'n; 'm} >> ->
                     push_lof_bind_nth_prefix p_bind t_bind
                     thenC termC (push_bind z (mk_subterm1_addr addr))
                | << lof_nth_suffix{i. 'f; 'j; 'n; 'm} >> ->
                     push_lof_bind_nth_suffix p_bind t_bind
                     thenC termC (push_bind z (mk_subterm1_addr addr))
                | << lof_append{i. 'f; j. 'g; 'k; 'n; 'm} >> ->
                     push_lof_bind_append p_bind t_bind
                     thenC termC (push_bind z (mk_subterm1_addr addr))
                     thenC termC (push_bind z (mk_subterm2_addr addr))
                | _ ->
                     idC
         else
            raise (RefineError ("push_bind", StringTermError ("not a lof_bind term", t_bind)))
   else
      raise (RefineError ("push_bind", StringTermError ("not a lof term", t)))

let push_bind_conv t =
   if is_lof_term t then
      let t = standardize t in
      let z = maybe_new_var_set var_z (all_vars t) in
         foldC t idC
         thenC termC (push_bind z (make_address []))
   else
      raise (RefineError ("push_bind_conv", StringTermError ("not a lof term", t)))

let pushLofBindC = termC push_bind_conv

(************************************************************************
 * Bind forms.
 *)
doc <:doc<
   Convert the expression in a << bind{'n; x. 'e['x]} >> to lof form.
>>
interactive_rw bindn_to_lof_bind :
   'n in nat -->
   bind{'n; x. 'e['x]}
   <-->
   lof_bind{'n; x. 'e[lof{i. lof_nth{'x; 'i}; 'n}]}

interactive_rw bind_to_lof_bind :
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

interactive_rw reduce_lof_bind_mk_bterm :
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
         thenC coalesce_bindn_bindn
         thenC bindn_to_lof_bind
      else
         raise (RefineError ("coalesce_bind", StringTermError ("not a nested bind", t)))

let coalesce_bindC = termC coalesce_bind

(************************************************************************
 * Constant reductions.
 *
 * XXX: JYH: I'm not to sure about constant reductions--I believe they
 * are too fragile.
 *)
doc <:doc<
   Constant reductions.
>>
interactive_rw reduce_nth_lof {| normalize_lof |} :
   'n in nat -->
   'j in nat -->
   'j < 'n -->
   lof_nth{lof{i. 'f['i]; 'n}; 'j}
   <-->
   'f['j]

interactive_rw reduce_nth_suffix_const {| normalize_lof |} :
   'j in nat -->
   lof_nth_suffix{i. 'f['i]; 'j; 'n; 'm}
   <-->
   'f['j +@ 'm]

(************************************************************************
 * Optimizations.
interactive_rw reduce_append_prefix_singleton {| normalize_lof |} :
   'n5 in nat -->
   lof{i. lof_append{j1. lof_nth_prefix{j2. lof_nth{'x; 'j2}; 'j1; 'n1; 'n2};
                     j2. lof_singleton{lof_nth{'x; 'n2}};
                     'i; 'n3; 'n4}; 'n5}
   <-->
   lof{i. lof_nth{'x; 'i}; 'n5}
 *)

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
