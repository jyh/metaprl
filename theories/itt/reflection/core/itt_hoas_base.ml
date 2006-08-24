doc <:doc<
   @module[Itt_hoas_base]
   The @tt[Itt_hoas_base] module defines the basic operations of the
   Higher Order Abstract Syntax (HOAS).

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

   Author: Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>

doc <:doc< @parents >>
extends Base_theory

extends Itt_dfun
extends Itt_union
extends Itt_prod
extends Itt_list2
doc docoff

open Basic_tactics
open Itt_dfun

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @terms
   The expression <<bind{x.'t['x]}>> represents a ``bound'' term (``bterm'')
   with a potentially free variable $x$. In order for it to be well-formed,
   $t$ must be a ``substitution function''.

   The <<mk_term{'op; 'subterms}>> expression represents a term with the operator
   <<'op>> and subterms $subterms$. In order for it to be well-formed, the length of
   $subterms$ must equal the arity of <<'op>> and each subterm must have the ``binding
   depth'' (i.e. the number of outer binds) equal to the corresponding number in the
   shape of <<'op>> (remember, the shape of an operator is a list of natural numbers
   and the length of the list is the operator's arity).

   The expression <<subst{'bt; 't}>> represents the result of substituting $t$
   for the first binding in <<'bt>>.

   Finally, the @tt[weak_dest_bterm] operator allows testing whether a term is a @tt[bind]
   or a @tt[mk_term] and to get the <<'op>> and $subterms$ in the latter case.
>>

define opaque unfold_bind:
   bind{x.'t['x]} <--> inl{lambda{x.'t['x]}}

define iform bind_list: bind_list{'terms} <--> map{bt. bind{x.'bt}; 'terms}

define opaque unfold_mk_term:
   mk_term{'op; 'subterms} <--> inr{('op, 'subterms)}

declare illegal_subst

define opaque unfold_subst:
   subst{'bt; 't} <--> decide{'bt; f. 'f 't; opt. illegal_subst}

define iform subst_list: subst_list{'terms;'v} <-->  map{bt. subst{'bt; 'v}; 'terms}

define opaque unfold_wdt:
   weak_dest_bterm{'bt; 'bind_case; op, sbt. 'mkterm_case['op; 'sbt]}
   <-->
   decide{'bt; f. 'bind_case; opt. spread{'opt; op, sbt. 'mkterm_case['op; 'sbt]}}

doc rewrites

interactive_rw reduce_subst {| reduce |} :
   subst{bind{x.'bt['x]}; 't} <--> 'bt['t]

interactive_rw reduce_wdt_bind {| reduce |} :
   weak_dest_bterm{bind{x.'t['x]}; 'bind_case; op, sbt. 'mkterm_case['op; 'sbt]} <--> 'bind_case

interactive_rw reduce_wdt_mk_term {| reduce |} :
   weak_dest_bterm{mk_term{'op; 'subterms}; 'bind_case; o, sbt. 'mkterm_case['o; 'sbt]}
   <-->
   'mkterm_case['op; 'subterms]

doc <:doc<
   On occasion, it is also useful to work with subterm lists directly, without
   the operator.  Define another constructor << mk_terms{'l} >> that represents
   a list of terms << 'l >>.
>>
define opaque unfold_mk_terms :
   mk_terms{'l} <--> inr{'l}

define unfold_weak_dest_terms :
   weak_dest_terms{'bt; 'bind_case; l. 'terms_case['l]}
   <-->
   decide{'bt; x. 'bind_case; y. 'terms_case['y]}

interactive_rw reduce_weak_dest_terms_bind {| reduce |} :
   weak_dest_terms{bind{x. 't['x]}; 'bind_case; terms. 'terms_case['terms]}
   <-->
   'bind_case

interactive_rw reduce_weak_dest_terms_mk_term {| reduce |} :
   weak_dest_terms{mk_term{'op; 'subterms}; 'bind_case; terms. 'terms_case['terms]}
   <-->
   'terms_case[('op, 'subterms)]

interactive_rw reduce_weak_dest_terms_mk_terms {| reduce |} :
   weak_dest_terms{mk_terms{'l}; 'bind_case; terms. 'terms_case['terms]}
   <-->
   'terms_case['l]

doc docoff

dform bind_df : parens :: "prec"[prec_lambda] :: bind{x.'t} =
   szone pushm[3] `"B " 'x `"." hspace slot{'t} popm ezone

dform bind_list_df : parens :: "prec"[prec_lambda] :: bind_list{'t} =
   szone pushm[3] `"B" hspace slot{'t} popm ezone

dform subst_df : parens :: "prec"[prec_apply] :: subst{'bt; 't} =
   slot["lt"]{'bt} `"@" slot["le"]{'t}

dform subst_list_df : parens :: "prec"[prec_apply] :: subst_list{'bt; 't} = subst{'bt; 't}

dform mk_term_df : mk_term{'op; 'subterms} =
   pushm[0] szone pushm[3] `"T(" slot{'op} `";" hspace slot{'subterms} popm `")" ezone popm

dform wdt_df : weak_dest_bterm{'bt; 'bind_case; op, sbt. 'mkterm_case} =
   pushm[0] szone szone pushm[3] keyword["match"] hspace slot{'bt} popm hspace ezone pushm[1] pushm[3]
   keyword["with"] hspace pushm[3] `"B _ -> " slot{'bind_case} popm popm hspace
   `"| " pushm[3] mk_term{'op; 'sbt} `" -> " slot{'mkterm_case} popm popm ezone popm

(************************************************************************
 * Tactics.
 *)
let bind_term = << bind{x. 'e['x]} >>
let bind_opname = opname_of_term bind_term
let is_bind_term = is_dep1_term bind_opname
let dest_bind_term = dest_dep1_term bind_opname
let mk_bind_term = mk_dep1_term bind_opname

let mk_term_term = << mk_term{'op; 'subterms} >>
let mk_term_opname = opname_of_term mk_term_term
let is_mk_term_term = is_dep0_dep0_term mk_term_opname
let dest_mk_term_term = dest_dep0_dep0_term mk_term_opname
let mk_mk_term_term = mk_dep0_dep0_term mk_term_opname
