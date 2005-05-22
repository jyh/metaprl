doc <:doc<
   @begin[doc]
   @module[Itt_hoas_vector]
   The @tt[Itt_hoas_vector] module defines the ``vector bindings''
   extensions for the basic ITT HOAS.
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
extends Itt_hoas_base
extends Itt_nat
extends Itt_list2
extends Itt_fun2
doc docoff

open Basic_tactics
open Itt_rfun
open Itt_list

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @terms
   The <<bind{'n; x.'t['x]}>> expression, where $n$ is a natural number,
   represents a ``telescope'' of $n$ nested @tt[bind] operations. Namely, it
   stands for <<bind{v_0.bind{v_1.math_ldots bind{v_n.'t['v0::'v1::math_ldots::'v_n::nil]}}}>>.

   We also provide an input form <<bind{'n; 't}>> for the important case of a vector
   binding that introduces a variable that does not occur freely in the bterm body.

   The <<subst{'n; 'bt; 't}>> expression represents the result of substituting term
   $t$ for the $n+1$-st variable of the bterm $bt$.

   @end[doc]
>>

define (*private*) unfold_bindn:
   bind{'n; x.'t['x]} <-->
   ind{'n; lambda{f. 'f nil}; "_", r. lambda{f. bind{v. 'r (lambda{l. 'f ('v :: 'l)})}}} lambda{x.'t['x]}

define (*private*) unfold_substn:
   subst{'n; 'bt; 't} <-->
   ind{'n; lambda{bt. subst{'bt; 't}}; "_", r. lambda{bt. bind{v. 'r subst{'bt; 'v}}}} 'bt

declare iform bind{'n; 't}

iform simple_bindn: bind{'n; 't} <-->  bind{'n; "_".'t}

doc "doc"{rewrites}

interactive_rw reduce_bindn_base {| reduce |} :
   bind{0; x.'t['x]} <--> 't[nil]

interactive_rw reduce_bindn_up {| reduce |} :
   'n in nat -->
   bind{'n +@ 1; l.'t['l]} <--> bind{v. bind{'n; l. 't['v :: 'l]}}

interactive_rw bind_into_bindone :
   bind{v. 't['v]} <--> bind{1; l. 't[hd{'l}]}

interactive_rw split_bind_sum :
   'm in nat -->
   'n in nat -->
   bind{'m +@ 'n; l. 't['l]} <-->
   bind{'m; l1. bind{'n; l2. 't[append{'l1;'l2}]}}

interactive_rw merge_bindn {| reduce |} :
   'm in nat -->
   'n in nat -->
   bind{'m; bind{'n; 't }} <--> bind{'m +@ 'n; 't }

interactive_rw reduce_substn_base {| reduce |} :
   subst{0; 'bt; 't} <--> subst{'bt; 't}

interactive_rw reduce_substn_case {| reduce |} :
   'n in nat -->
   subst{'n +@ 1; 'bt; 't} <--> bind{x. subst{'n; subst{'bt; 'x}; 't}}

interactive_rw reduce_bindn_subst {| reduce |} :
   'n in nat -->
    subst{bind{'n +@ 1; v. 'bt['v]}; 't} <--> bind{'n; v. 'bt['t :: 'v]}

interactive_rw reduce_substn_bindn1 Perv!bind{x.'bt['x]} :
   'm in nat -->
   'n in nat -->
   'n >= 'm -->
   subst{'m; bind{v. bind{'n; l.'bt['v::'l]}}; 't} <--> bind{'n; l. 'bt[insert_at{'l; 'm; 't}]}

doc docoff

let bind_opname = opname_of_term <<bind{v.'t}>>
let bindn_opname = opname_of_term <<bind{'n; v.'t}>>

let rsbC = termC (fun t ->
   let _, b, _ = three_subterms t in
   let v, b = dest_dep1_term bind_opname b in
   let l, _, bt = dest_dep0_dep1_term bindn_opname b in
   let bind = var_subst_to_bind bt (mk_cons_term (mk_var_term v) (mk_var_term l)) in
      reduce_substn_bindn1 bind)

let resource reduce +=
   << subst{'m; bind{v. bind{'n; l.'bt['v::'l]}}; 't} >>, rsbC

doc docon

interactive_rw reduce_substn_bindn2 {| reduce |} :
   'm in nat -->
   'n in nat -->
   'n >= 'm -->
   subst{'m; bind{'n +@ 1; l.'bt['l]}; 't} <--> bind{'n; l. 'bt[insert_at{'l; 'm; 't}]}

doc docoff

dform bind_df : "prec"[prec_apply] :: mode[prl] :: bind{'n; x.'t} =
   szone pushm[3] `"B^" slot["le"]{'n} space 'x `"." slot["le"]{'t} popm ezone

dform bind_df2 : mode[html] :: mode[tex] :: bind{'n; x.'t} =
   szone pushm[3] `"B" sup{slot{'n}} space 'x `"." slot["le"]{'t} popm ezone

dform subst_df : parens :: "prec"[prec_apply] :: mode[prl] :: subst{'n; 'bt; 't} =
   szone pushm[3] slot["lt"]{'bt} `" @(" slot["none"]{'n} `")" space slot["le"]{'t} popm ezone

dform subst_df2 : parens :: "prec"[prec_apply] :: mode[html] :: mode[tex] :: subst{'n; 'bt; 't} =
   szone pushm[3] slot["lt"]{'bt} `" @" sub{slot["none"]{'n}} space slot["le"]{'t} popm ezone

