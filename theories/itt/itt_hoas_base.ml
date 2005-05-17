doc <:doc<
   @begin[doc]
   @module[Itt_hoas_base]
   The @tt[Itt_hoas_base] module defines the basic operations of the
   Higher Order Abstract Syntax (HOAS).
   @end[doc]

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

doc <:doc< @doc{parents} >>
extends Base_theory

extends Itt_fun
extends Itt_union
extends Itt_prod
doc docoff

open Basic_tactics
open Itt_rfun

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @terms
   The <<bind{x.'t['x]}>> expression represents a ``bound'' term (``bterm'')
   with a potentially free variable $x$. In order for it to be well-formed,
   $t$ must be a ``substitution function''.

   The <<mk_term{'op; 'subterms}>> expression represents a term with the operator
   $op$ and subterms $subterms$. In order for it to be well-formed, the length of
   $subterms$ must equal the arity of $op$ and each subterm must have the ``binding
   depth'' (i.e. the number of outer binds) equal to the corresponding number in the
   shape of $op$ (remember, the shape of an operator is a list of natural numbers
   and the length of the list is the operator's arity).

   The expression <<subst{'bt; 't}>> represents the result of substituting $t$
   for the first binding in $bt$.

   Finally, the @tt[weak_dest_bterm] operator allows testing whether a term is a @tt[bind]
   or a @tt[mk_term] and to get the $op$ and $subterms$ in the latter case.
   @end[doc]
>>

define (*private*) unfold_bind:
   bind{x.'t['x]} <--> inl{lambda{x.'t['x]}}

define (*private*) unfold_mk_term:
   mk_term{'op; 'subterms} <--> inr{('op, 'subterms)}

declare illegal_subst

define (*private*) unfold_subst:
   subst{'bt; 't} <--> decide{'bt; f. 'f 't; opt. illegal_subst}

define (*private*) unfold_wdt:
   weak_dest_bterm{'bt; 'bind_case; op, sbt. 'mkterm_case['op; 'sbt]}
   <-->
   decide{'bt; f. 'bind_case; opt. spread{'opt; op, sbt. 'mkterm_case['op; 'sbt]}}

doc "doc"{rewrites}

interactive_rw reduce_subst {| reduce |} :
   subst{bind{x.'bt['x]}; 't} <--> 'bt['t]

interactive_rw reduce_wdt_bind {| reduce |} :
   weak_dest_bterm{bind{x.'t['x]}; 'bind_case; op, sbt. 'mkterm_case['op; 'sbt]} <--> 'bind_case

interactive_rw reduce_wdt_mk_term {| reduce |} :
   weak_dest_bterm{mk_term{'op; 'subterms}; 'bind_case; o, sbt. 'mkterm_case['o; 'sbt]}
   <-->
   'mkterm_case['op; 'subterms]

doc docoff

dform bind_df : parens :: "prec"[prec_lambda] :: bind{x.'t} =
   `"B " 'x `"." slot{'t}

dform subst_df : parens :: "prec"[prec_apply] :: subst{'bt; 't} =
   slot["lt"]{'bt} `"@" slot["le"]{'t}

dform mk_term_df : mk_term{'op; 'subterms} =
   pushm[0] szone pushm[3] `"T(" slot{'op} `";" hspace slot{'subterms} popm `")" ezone popm

dform wdt_df : weak_dest_bterm{'bt; 'bind_case; op, sbt. 'mkterm_case} =
   szone pushm[1] pushm[3] `"match" " " slot{'bt} " " `"with" hspace
   pushm[3] `"B _ -> " slot{'bind_case} popm popm hspace
   `"| " pushm[3] mk_term{'op; 'sbt} `" -> " slot{'mkterm_case} popm popm ezone

