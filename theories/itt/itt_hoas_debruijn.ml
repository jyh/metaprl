doc <:doc<
   @begin[doc]
   The @tt[Itt_hoas_debruij] module defines a mapping from deBruijn-like
   representation of syntax into the HOAS.
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

doc <:doc< @doc{@parents} >>
extends Itt_hoas_base
extends Itt_hoas_vector
extends Itt_nat
extends Itt_list2

doc docoff

open Basic_tactics
open Itt_rfun

doc <:doc<
   @begin[doc]
   @terms
   @modsubsection{deBruijn-like representation of syntax}
   Our deBruijn-like representation of (bound) terms consists of two operators. <<var{'left; 'right}>>
   represents a variable bterm, whose ``left index'' is <<'left>> and whose ``right index'' is <<'right>>.
   Namely, it represent the term
   <<bind{x_1.math_ldots bind{x_left.bind{y.bind{z_1.math_ldots bind{z_right. 'v} math_ldots}}} math_ldots}>>.

   The <<mk_bterm{'n; 'op; 'btl}>> represents the compound term of depth $n$. In oder words,
   <<mk_bterm{'n; 'op; (bind{'n; v.'bt_1['v]} :: math_ldots :: bind{'n; v.'bt_k['v]}::nil)}>> is
   <<bind{'n; v. mk_term{'op; ('bt_1['v] :: math_ldots :: 'bt_k['v]::nil)}}>>.
   @end[doc]
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
   <<depth{'bt}>> is the ``binding depth'' (i.e. the numbere of outer bindings) of a bterm <<'bt>>.
>>

define unfold_depth:
   depth{'bt} <--> fix{f.lambda{bt. weak_dest_bterm{'bt; 1 +@ 'f subst{'bt; mk_term{it; nil}}; "_", "_". 0}}} 'bt

doc <:doc< @doc{@rewrites} >>

interactive_rw reduce_mk_bterm_base {| reduce |}:
   mk_bterm{0; 'op; 'btl} <--> mk_term{'op; 'btl }

interactive_rw reduce_mk_bterm_step {| reduce |}:
   'n in nat -->
   mk_bterm{'n +@ 1; 'op; 'btl} <--> bind{v. mk_bterm{'n; 'op; map{bt. subst{'bt; 'v}; 'btl}}}

interactive_rw reduce_mk_bterm_empty {| reduce |}:
   'n in nat -->
   mk_bterm{'n; 'op; nil} <--> bind{'n; mk_term{'op; nil}}

interactive_rw reduce_depth_mk_term {| reduce |}:
   depth{mk_term{'op; 'btl}} <--> 0

interactive_rw reduce_depth_bind {| reduce |} :
   depth{bind{v.'t['v]}} <--> 1 +@ depth{'t[mk_term{it; nil}]}

interactive_rw reduce_depth_var {| reduce |} :
   'l in nat -->
   'r in nat -->
   depth{var{'l; 'r}} <--> 'l +@ 'r +@ 1

interactive_rw reduce_depth_mk_bterm {| reduce |} :
   'n in nat -->
   depth{mk_bterm{'n; 'op; 'btl}} <--> 'n

doc docoff

dform var_df : var{'l; 'r} =
   pushm[3] tt["var"] `"(" slot{'l} `"," slot{'r} `")" popm

dform mk_bterm_df : mk_bterm{'n; 'op; 'btl} =
   szone pushm[3] tt["mk_bterm"] `"(" slot{'n} `";" hspace slot{'op} `";" hspace slot{'btl} `")" popm ezone

dform depth_df: parens :: "prec"[prec_apply] :: depth{'bt} =
   tt["D"] space slot["le"]{'bt}
