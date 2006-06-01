doc <:doc<
   @module[Itt_hoas_vector]
   The @tt[Itt_hoas_vector] module defines the ``vector bindings''
   extensions for the basic ITT HOAS.

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
extends Itt_hoas_base
extends Itt_nat
extends Itt_list2
extends Itt_fun2
extends Itt_list3
doc docoff

open Basic_tactics
open Itt_dfun
open Itt_list

(*
 * Reduce control.
 *)
declare denormalize : SelectOption

let denormalize_term = << select["denormalize":t] >>

let denormalize_labels = [denormalize_term]

let resource select +=
   denormalize_term, OptionExclude

let resource private select +=
   denormalize_term, OptionAllow

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @terms
   The <<bind{'n; x.'t['x]}>> expression, where <<'n>> is a natural number,
   represents a ``telescope'' of $n$ nested @tt[bind] operations. Namely, it
   stands for <<bind{v_1.bind{v_2.math_ldots bind{v_n.'t['v1::'v2::math_ldots::'v_n::nil]}}}>>.

   We also provide an input form <<bind{'n; 't}>> for the important case of a vector
   binding that introduces a variable that does not occur freely in the bterm body.

   The <<subst{'n; 'bt; 't}>> expression represents the result of substituting term
   <<'t>> for the <<'n+@1>>-@misspelled{st} binding of the bterm <<'bt>>.

   The <<substl{'bt; 'tl}>> expression represents the result of simultaneous substitution
   of terms <<'tl>> (<<'tl>> must be a list) for the first <<length{'tl}>> bindings of the
   bterm <<'bt>>.

>>

define (*private*) unfold_bindn:
   bind{'n; x.'t['x]} <-->
   ind{'n; lambda{f. 'f nil}; "_", r. lambda{f. bind{v. 'r (lambda{l. 'f ('v :: 'l)})}}} lambda{x.'t['x]}

define (*private*) unfold_substn:
   subst{'n; 'bt; 't} <-->
   ind{'n; lambda{bt. subst{'bt; 't}}; "_", r. lambda{bt. bind{v. 'r subst{'bt; 'v}}}} 'bt

define (*private*) unfold_substl:
   substl{'bt; 'tl} <-->
   list_ind{'tl; lambda{b.'b}; h, "_", f. lambda{b. 'f subst{'b; 'h}}} 'bt

define iform simple_bindn: bind{'n; 't} <-->  bind{'n; "_".'t}

doc rewrites

interactive_rw reduce_bindn_base {| reduce |} :
   bind{0; x.'t['x]} <--> 't[nil]

(*
 * This is a denormalization rule, incompatible with Itt_hoas_normalize.
 * Normally, prevent it from running.
 *)
interactive_rw reduce_bindn_up {| reduce ~labels:denormalize_labels |} :
   'n in nat -->
   bind{'n +@ 1; l.'t['l]} <--> bind{v. bind{'n; l. 't['v :: 'l]}}

interactive_rw reduce_bindn_upleft :
   'n in nat -->
   bind{1 +@ 'n; l.'t['l]} <--> bind{v. bind{'n; l. 't['v :: 'l]}}

interactive_rw bind_into_bindone :
   bind{v. 't['v]} <--> bind{1; l. 't[hd{'l}]}

interactive_rw bindone_into_bind :
   bind{1; l. 't['l]}
   <-->
   bind{v. 't[cons{'v; nil}]}

interactive_rw split_bind_sum :
   'm in nat -->
   'n in nat -->
   bind{'m +@ 'n; l. 't['l]} <-->
   bind{'m; l1. bind{'n; l2. 't[append{'l1;'l2}]}}

interactive_rw reduce_bindn_right :
   'n in nat -->
   bind{'n +@ 1; l. 't['l]} <--> bind{'n; l. bind{v. 't[append{'l; cons{'v; nil}}]}}

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
   << subst{'m; bind{v. bind{'n; l.'bt['v::'l]}}; 't} >>, wrap_reduce_crw rsbC

doc docon

interactive_rw reduce_substn_bindn2 {| reduce |} :
   'm in nat -->
   'n in nat -->
   'n >= 'm -->
   subst{'m; bind{'n +@ 1; l.'bt['l]}; 't} <--> bind{'n; l. 'bt[insert_at{'l; 'm; 't}]}

interactive_rw reduce_substl_base {| reduce |} :
   substl{'bt; nil} <--> 'bt

(*
 * XXX: JYH: the following rule is also denormalization rules.
 *)
interactive_rw reduce_substl_step {| reduce ~labels:denormalize_labels |} :
   substl{'bt; 'h :: 't} <--> substl{subst{'bt;'h}; 't}

interactive_rw reduce_substl_step1 {| reduce |} :
   substl{bind{v. 'bt['v]}; 'h :: 't} <--> substl{'bt['h]; 't}

interactive_rw reduce_substl_step2 {| reduce |} :
   'n in nat -->
   substl{bind{'n +@ 1; v. 'bt['v]}; 'h :: 't} <--> substl{bind{'n; v. 'bt['h::'v]}; 't}

interactive_rw reduce_substl_bindn1 {| reduce |} :
   'l in list -->
   substl{bind{length{'l}; v.'bt['v]}; 'l} <--> 'bt['l]

interactive_rw reduce_substl_bindn2 :
   'l in list -->
   'n in nat -->
   'n >= length{'l} -->
   substl{bind{'n; v.'bt['v]}; 'l} <--> bind{'n -@ length{'l}; v. 'bt[append{'l; 'v}]}

interactive_rw reduce_bsb1 {| reduce |} :
   'n in nat -->
   bind{'n; v. substl{bind{'n; w.'bt['w]}; 'v}} <--> bind{'n; w.'bt['w]}

interactive_rw reduce_bsb2 {| reduce |} :
   'n in nat -->
   'm in nat -->
   bind{'n; v. substl{bind{'n +@ 'm; w.'bt['w]}; 'v}} <--> bind{'n +@ 'm; w.'bt['w]}

interactive_rw unfold_bindnsub :
   'n in nat -->
   bind{'n +@ 1; v. substl{'bt['v]; 'v}} <--> bind{u.bind{'n; v. substl{subst{'bt['u :: 'v]; 'u}; 'v}}}

(*
 * Additional theorems for subst association.
 *)
interactive_rw subst_to_substl :
   subst{'e; 'x}
   <-->
   substl{'e; cons{'x; nil}}

interactive_rw bindn_to_list_of_fun :
   'n in nat -->
   bind{'n; x. 'e['x]}
   <-->
   bind{'n; x. 'e[list_of_fun{i. nth{'x; 'i}; 'n}]}

interactive_rw coalesce_bindn_bindn :
   'n in nat -->
   'm in nat -->
   bind{'n; x. bind{'m; y. 'e['x; 'y]}}
   <-->
   bind{'n +@ 'm; x. 'e[nth_prefix{'x; 'n}; nth_suffix{'x; 'n}]}

interactive_rw substl_append_right :
   'l in list -->
   substl{'e; append{'l; cons{'x; nil}}}
   <-->
   subst{substl{'e; 'l}; 'x}

interactive_rw substl_append_left :
   'l in list -->
   substl{subst{'e; 'x}; 'l}
   <-->
   substl{'e; cons{'x; 'l}}

interactive_rw substl_substl_list :
   'l1 in list -->
   'l2 in list -->
   substl{substl{'e; 'l1}; 'l2}
   <-->
   substl{'e; append{'l1; 'l2}}

interactive_rw substl_substl_lof:
   'n in nat -->
   'm in nat -->
   substl{substl{'e; list_of_fun{x. 'f['x]; 'm}}; list_of_fun{x. 'g['x]; 'n}}
   <-->
   substl{'e; append{list_of_fun{x. 'f['x]; 'm}; list_of_fun{x. 'g['x]; 'n}}}

doc docoff

dform bind_df : "prec"[prec_apply] :: mode[prl] :: bind{'n; x.'t} =
   szone pushm[3] `"B^" 'x `":" slot["le"]{'n} "." hspace slot["le"]{'t} popm ezone

dform bind_df2 : mode[html] :: mode[tex] :: bind{'n; x.'t} =
   szone pushm[3] `"B " 'x `":" sup{slot{'n}} `"." hspace slot["le"]{'t} popm ezone

dform subst_df : parens :: "prec"[prec_apply] :: mode[prl] :: subst{'n; 'bt; 't} =
   szone pushm[3] slot["lt"]{'bt} `" @(" slot["none"]{'n} `")" hspace slot["le"]{'t} popm ezone

dform subst_df2 : parens :: "prec"[prec_apply] :: mode[html] :: mode[tex] :: subst{'n; 'bt; 't} =
   szone pushm[3] slot["lt"]{'bt} `" @" sub{slot["none"]{'n}} hspace slot["le"]{'t} popm ezone

dform substl_df : parens :: "prec"[prec_apply] :: substl{'bt; 'tl} =
      slot["lt"]{'bt} `"@" Mpsymbols!subl slot["le"]{'tl}

(************************************************************************
 * Tactics.
 *)
let bindn_term = << bind{'n; x. 'e['x]} >>
let bindn_opname = opname_of_term bindn_term
let is_bindn_term = is_dep0_dep1_term bindn_opname
let dest_bindn_term = dest_dep0_dep1_term bindn_opname
let mk_bindn_term = mk_dep0_dep1_term bindn_opname

let substl_term = << substl{'e1; 'e2} >>
let substl_opname = opname_of_term substl_term
let is_substl_term = is_dep0_dep0_term substl_opname
let dest_substl_term = dest_dep0_dep0_term substl_opname
let mk_substl_term = mk_dep0_dep0_term substl_opname

let subst_term = << subst{'e1; 'e2} >>
let subst_opname = opname_of_term subst_term
let is_subst_term = is_dep0_dep0_term subst_opname
let dest_subst_term = dest_dep0_dep0_term subst_opname
let mk_subst_term = mk_dep0_dep0_term subst_opname

let reduceBTermC =
   withOptionC denormalize_term "allow" reduceC

let reduceBTermT =
   rwAll reduceBTermC

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
