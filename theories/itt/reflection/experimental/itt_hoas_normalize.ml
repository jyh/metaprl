doc <:doc<
   @module[Itt_hoas_normalize]

   The @tt[Itt_hoas_normalize] module defines a normalization procedure
   for BTerms.  Here are the rules.

   @begin[itemize]
   @item{{All << mk_term{'op; 'subterms} >> are converted to << mk_bterm{0; 'op; 'subterms} >>.}}
   @item{{All << bind{x. 'e['x]} >> are converted to << bind{1; x. 'e[cons{'x; nil}]} >>.}}
   @item{{All nested binds are coalesced.}}
   @item{{All binds are pushed down into subterms as far as possible.}}
   @end[itemize]

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
extends Itt_hoas_bterm
extends Itt_hoas_util
extends Itt_vec_list1
extends Itt_vec_bind
extends Itt_list3

doc docoff

open Lm_printf
open Basic_tactics
open Itt_vec_list1
open Itt_hoas_base
open Itt_hoas_vector
open Itt_hoas_debruijn
open Itt_equal

(************************************************************************
 * Subterm bind lists.
 *)
doc <:doc<
   The term << subterms_bind{'e} >> transforms a binding around a list
   << bind{x. cons{'e1['x]; math_ldots}} >> to a list of
   binds << cons{bind{x. 'e1['x]}; math_ldots} >>.
>>
define unfold_subterms_length : subterms_length{'e} <--> <:xterm<
   (fix f e -> weak_dest_terms{e; f subst{e; "it"}; l. length{l}}) e
>>

define unfold_subterms_nth : subterms_nth{'e; 'i} <--> <:xterm<
   (fix f e -> weak_dest_terms{e; bind{x. f subst{e; x}}; l. nth{l; i}}) e
>>

define unfold_subterms_bind : subterms_bind{'e} <--> <:xterm<
   list_of_fun{k. subterms_nth{e; k}; subterms_length{e}}
>>

doc docoff

let fold_subterms_length = makeFoldC << subterms_length{'e} >> unfold_subterms_length
let fold_subterms_nth = makeFoldC << subterms_nth{'e; 'i} >> unfold_subterms_nth
let fold_subterms_bind = makeFoldC << subterms_bind{'e} >> unfold_subterms_bind

(************************************************
 * Term reductions.
 *)
interactive_rw reduce_subterms_bind {| reduce |} : <:xrewrite<
   subterms_length{bind{x. e[x]}}
   <-->
   subterms_length{e["it"]}
>>

interactive_rw reduce_subterms_terms {| reduce |} : <:xrewrite<
   subterms_length{mk_terms{e}}
   <-->
   length{e}
>>

interactive_rw reduce_subterms_bindn {| reduce |} : <:xrewrite<
   n IN "nat" -->
   subterms_length{bind{n; x. mk_terms{"vlist"{| <J[x]> |}}}}
   <-->
   length{"vlist"{| <J["it"]> |}}
>>

interactive_rw reduce_subterms_nth_bind {| reduce |} : <:xrewrite<
   subterms_nth{bind{x. e[x]}; i}
   <-->
   bind{x. subterms_nth{e[x]; i}}
>>

interactive_rw reduce_subterms_nth_bindn {| reduce |} : <:xrewrite<
   n IN "nat" -->
   subterms_nth{bind{n; x. e[x]}; i}
   <-->
   bind{n; x. subterms_nth{e[x]; i}}
>>

interactive_rw reduce_subterms_nth_mk_terms {| reduce |} : <:xrewrite<
   subterms_nth{mk_terms{e}; i}
   <-->
   nth{e; i}
>>

(************************************************
 * Step-by-step reductions.
 *)
doc <:doc<
   For concrete << subterms_bind{bind{x. mk_terms{vlist{| 'e_1['x]; math_ldots; 'e_n['x] |}}}} >>,
   define a step-by-step reduction.
>>
interactive_rw reduce_subterms_bind1_nil {| reduce |} : <:xrewrite<
   subterms_bind{bind{x. mk_terms{"vlist"{||}}}}
   <-->
   []
>>

interactive_rw reduce_subterms_bind1_cons {| reduce |} : <:xrewrite<
   subterms_bind{bind{x. mk_terms{"vlist"{| A[x]; <J[x]> |}}}}
   <-->
   bind{x. A[x]} :: subterms_bind{bind{x. mk_terms{"vlist"{| <J[x]> |}}}}
>>

interactive_rw reduce_subterms_bindn_nil {| reduce |} : <:xrewrite<
   n IN "nat" -->
   subterms_bind{bind{n; x. mk_terms{"vlist"{||}}}}
   <-->
   []
>>

interactive_rw reduce_subterms_bindn_cons {| reduce |} : <:xrewrite<
   n IN "nat" -->
   subterms_bind{bind{n; x. mk_terms{"vlist"{| A[x]; <J[x]> |}}}}
   <-->
   bind{n; x. A[x]} :: subterms_bind{bind{n; x. mk_terms{"vlist"{| <J[x]> |}}}}
>>

(************************************************************************
 * The bind pushing theorems.
 *)
interactive_rw reduce_list_of_fun_of_bind_vlist {| reduce |} :
   list_of_fun{i. bind{x. nth{vlist{| <J['x]> |}; 'i}}; length{vlist{| <J[it]> |}}}
   <-->
   subterms_bind{bind{x. mk_terms{vlist{| <J['x]> |}}}}

interactive_rw reduce_list_of_fun_of_bindn_vlist {| reduce |} :
   'n in nat -->
   list_of_fun{i. bind{'n; x. nth{vlist{| <J['x]> |}; 'i}}; length{vlist{| <J[it]> |}}}
   <-->
   subterms_bind{bind{'n; x. mk_terms{vlist{| <J['x]> |}}}}

interactive_rw reduce_bind_of_mk_bterm :
   'n in nat -->
   bind{x. mk_bterm{'n; 'op; vlist{| <J['x]> |}}}
   <-->
   mk_bterm{'n +@ 1; 'op; subterms_bind{bind{x. mk_terms{vlist{| <J['x]> |}}}}}

interactive_rw reduce_bindn_of_mk_bterm :
   'i in nat -->
   'n in nat -->
   bind{'i; x. mk_bterm{'n; 'op; vlist{| <J['x]> |}}}
   <-->
   mk_bterm{'n +@ 'i; 'op; subterms_bind{bind{'i; x. mk_terms{vlist{| <J['x]> |}}}}}

(************************************************************************
 * Tactics.
 *)
doc <:doc<
   The normalization conversion performs the following steps:
   @begin[enumerate]
   @item{{Eliminate all << mk_term{'op; 'subterms} >>.}}
   @item{{Eliminate all << bind{x. 'e['x]} >>.}}
   @end[enumerate]
   @docoff
>>

(*
 * Prepare the term by eliminating some of the simpler terms.
 *)
let pre_normalize_term =
   sweepUpC fold_mk_term
   thenC sweepUpC bindone_into_bind

(*
 * Push the bind into a list of concrete subterms.
 *)
let rec reduce_subterms_bindn t =
   (reduce_subterms_bindn_cons thenC addrC [Subterm 2] (termC reduce_subterms_bindn))
   orelseC reduce_subterms_bindn_nil

let push_bind_into_concrete_subterms =
   addrC [Subterm 2; Subterm 3] vlist_of_concrete_listC
   thenC reduce_bindn_of_mk_bterm
   thenC (addrC [Subterm 3] (termC reduce_subterms_bindn))

(*
 * Once the pre-normalization step is done,
 * the term we are looking at should be either
 *    1. A bindn term
 *    2. A mk_bterm term
 *
 * In the first case, coalesce all nested binds,
 * then push the binds into the subterms.
 *)
let rec normalize_bterm t =
   if is_bindn_term t then
      repeatC coalesce_bindn_bindn
      thenC tryC (push_bind_into_concrete_subterms thenC termC normalize_bterm)
   else if is_mk_bterm_term t then
      addrC [Subterm 3] (higherC (termC normalize_bterm))
   else
      raise (RefineError ("normalize_bterm", StringTermError ("unknown term", t)))

let normalizeBTermC =
   pre_normalize_term
   thenC (termC normalize_bterm)

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
