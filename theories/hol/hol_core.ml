(*
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2004 Mojave Group, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends Base_theory

open Basic_tactics

(*
 * Judgments.
 *)
declare member{'e; 't}
declare "type"{'t}
declare wf

(*
 * Terms.
 *)
declare equal{'e1; 'e2}
declare apply{'e1; 'e2}
declare lambda{'t; x. 'e['x]}

(*
 * Types.
 *)
declare bool
declare ind
declare "fun"{'t1; 't2}
declare ty

(*
 * Random stuff.
 *)
declare default_extract

(************************************************************************
 * Typing rules.
 *)
prim bool_intro {| intro [] |} :
   sequent { <H> >- "type"{bool} }

prim ind_intro {| intro [] |} :
   sequent { <H> >- "type"{ind} }

prim fun_intro {| intro [] |} :
   sequent { <H> >- "type"{'s} } -->
   sequent { <H> >- "type"{'t} } -->
   sequent { <H> >- "type"{'s -> 't} }

prim var_intro1 'H :
   sequent { <H>; x: 't; <J['x]> >- wf } -->
   sequent { <H>; x: 't; <J['x]> >- 'x IN 't }

prim var_intro2 {| nth_hyp |} 'H :
   sequent { <H>; x: ty; <J['x]> >- "type"{'x} }

prim lambda_intro {| intro [] |} :
   sequent { <H> >- "type"{'s} } -->
   sequent { <H>; x: 's >- 'e['x] IN 't } -->
      sequent { <H> >- lambda{'s; x. 'e['x]} IN 's -> 't }

prim eq_wf {| intro [intro_typeinf <<'x>>] |} 't :
   sequent { <H> >- 'x in 't } -->
   sequent { <H> >-  'y in 't } -->
   sequent { <H> >- ('x = 'y) in bool }

prim apply_wf {| intro [intro_typeinf << 'x >>] |} 's :
   sequent { <H> >- 'f in 's -> 't } -->
   sequent { <H> >- 'x in 's } -->
   sequent { <H> >- ('f 'x) in 't }

prim wf_nil :
   sequent { >- wf }

prim wf_cons :
   sequent { <H> >- wf } -->
   sequent { <H> >- "type"{'ty} } -->
   sequent { <H>; x: 'ty >- wf }

prim wf_ty :
   sequent { <H> >- wf } -->
   sequent { <H>; x: ty >- wf }

(************************************************************************
 * Core rules.
 *)
prim axiom 'H :
   sequent { <H>; <J> >- 'P in bool } -->
   sequent { <H>; 'P; <J> >- 'P }

(*
prim axiom2 :
   sequent { <H> >- 'P in bool } -->
   sequent { <H> >- sequent { <J>; <K> >- wf } } -->
   sequent { <H> >- sequent { <J>; 'P; <K> >- 'P } }
*)

prim reflexive 't :
   sequent { <H> >- 'e IN 't } -->
   sequent { <H> >- 'e = 'e }

prim transitive 't :
   sequent { <H> >- 's = 't } -->
   sequent { <H> >- 't = 'u } -->
   sequent { <H> >- 's = 'u }

prim pre_beta :
   [wf] sequent { <H> >- !y IN 't } -->
   sequent { <H> >- (lambda{'t; x. 'e['x]} !y) = 'e[!y] }

prim abs {| intro [] |} :
   sequent { <H> >- "type"{'t} } -->
   sequent { <H>; x: 't >- 'e1['x] = 'e2['x] } -->
   sequent { <H> >- lambda{'t; x. 'e1['x]} = lambda{'t; x. 'e2['x]} }

prim mk_comb ('s -> 't) :
   sequent { <H> >- 'x IN 's } -->
   sequent { <H> >- 'f IN 's -> 't } -->
   sequent { <H> >- 'f = 'g } -->
   sequent { <H> >- 'x = 'y } -->
   sequent { <H> >- ('f 'x) = ('g 'y) }

prim inst bind{x. 'P['x]} 'e 't :
   [wf] sequent { <H> >- 'e IN 't } -->
   sequent { <H>; x: 't >- 'P['x] } -->
   sequent { <H> >- 'P['e] }

(*
 * Question: is it important that the two premises
 * have different contexts?
 *)
prim ec_mp 'P :
   sequent { <H> >- 'P = 'Q } -->
   sequent { <H> >- 'P } -->
   sequent { <H> >- 'Q }

prim inst_type bind{x. 'P['x]} 't :
   [wf] sequent { <H> >- "type"{'t} } -->
   sequent { <H>; x: ty >- 'P['x] } -->
   sequent { <H> >- 'P['t] }

prim deduct_antisym :
   sequent { <H> >- 'P in bool } -->
   sequent { <H> >- 'Q in bool } -->
   sequent { <H>; 'Q >- 'P } -->
   sequent { <H>; 'P >- 'Q } -->
   sequent { <H> >- 'P = 'Q }

(************************************************************************
 * Logic.
 *)

define unfold_true  : "true" <--> (lambda{bool; x. 'x} = lambda{bool; x. 'x})
define unfold_all   : "all"{'ty} <--> lambda{'ty -> bool; P. 'P = lambda{'ty; x. "true"}}
define unfold_all2  : "all"{'ty; x. 'P['x]} <--> ("all"{'ty} lambda{'ty; x. 'P['x]})
define unfold_false : "false"  <--> "all"{bool; P. 'P}

define unfold_and   :
   "and"{'P1; 'P2}
   <-->
   lambda{bool -> bool -> bool; x. 'x 'P1 'P2} = lambda{bool -> bool -> bool; x. 'x "true" "true"}

define unfold_implies :
   "implies"{'P1; 'P2}
   <-->
   ('P1 & 'P2) = 'P1

define unfold_or :
   "or"{'P1; 'P2}
   <-->
   "all"{bool; Q. ('P1 -> 'Q) -> ('P2 -> 'Q) -> 'Q}

define unfold_not : "not"{'P} <--> 'P -> "false"

define unfold_exists1 :
   "exists"{'ty} <-->
      lambda {'ty -> bool; P. "all"{bool; Q. ("all" {'ty; x. ('P 'x) => 'Q } => 'Q)}}

(* lambda{'ty -> bool; P. "not"{'P = lambda{'ty; x. "false"}}} *)

define unfold_exists2 :
   "exists"{'ty; x. 'P['x]}
   <-->
   ("exists"{'ty} lambda{'ty; x. 'P['x]})

(************************************************************************
 * Extra axioms.
 *)
declare select{'t}

define unfold_select :
   select{'t; x. 'P['x]}
   <-->
   select{'t} lambda{'t; x. 'P['x]}

prim select :
   [wf] sequent { <H> >- 'e IN 't } -->
   [wf] sequent { <H> >- 'P IN 't -> bool } -->
   sequent { <H> >- 'P 'e => 'P (select{'t} 'P) }

prim eta :
   sequent { <H> >- lambda{'ty; x. 'e 'x} = 'e }

define unfold_injective :
   injective{'f}
   <-->
   "all"{ind; x. "all"{ind; y. ('f 'x = 'f 'y) => 'x = 'y }}

define unfold_surjective :
   surjective{'f}
   <-->
   "all"{ind; x. exists{ind; y. 'f 'y = 'x }}

prim inf :
   sequent { <H>; f: ind -> ind; injective{'f}; surjective{'f} >- 'P } -->
   sequent { <H> >- 'P }

(************************************************************************
 * Display.
 *)
prec prec_fun
prec prec_apply
prec prec_lambda
prec prec_lambda < prec_apply
prec prec_fun < prec_apply
prec prec_fun < prec_lambda

prec prec_equal
prec prec_equal < prec_apply

prec prec_iff
prec prec_implies
prec prec_and
prec prec_or
prec prec_not
prec prec_quant

prec prec_implies < prec_iff
prec prec_iff < prec_or
prec prec_or < prec_and
prec prec_and < prec_not
prec prec_quant < prec_iff

dform default_extract_df : default_extract =
   `""

dform member_df : parens :: "prec"[prec_equal] :: member{'e; 't} =
   szone pushm[0] slot{'e} hspace Nuprl_font!member `" " slot{'t} popm ezone

dform type_df : "type"{'t} =
   slot{'t} `" Type"

dform wf_df : "wf" =
   `"WF"

dform equal_df : parens :: "prec"[prec_equal] :: equal{'e1; 'e2} =
   szone pushm[0] slot{'e1} hspace `"= " slot{'e2} popm ezone

dform apply_df : parens :: "prec"[prec_apply] :: apply{'f; 'x} =
   slot["lt"]{'f} " " slot["le"]{'x}

dform lambda_df : parens :: "prec"[prec_lambda] :: lambda{'ty; x. 'e} =
   szone pushm[3] Nuprl_font!lambda slot{'x} `":" slot{'ty} `"." hspace slot{'e} popm ezone

dform bool_df : bool =
   mathbbB

dform ind_df : ind =
   Nuprl_font!omega

dform fun_df : parens :: "prec"[prec_fun] :: "fun"{'t1; 't2} =
   szone pushm[3] slot["le"]{'t1} hspace Nuprl_font!rightarrow `" " slot{'t2} popm ezone

dform ty_df : ty =
   Nuprl_font!Omega

dform true_df : "true" =
   `"True"

dform false_df : "false" =
   `"False"

dform not_df : parens :: "prec"[prec_not] :: "not"{'P} =
   szone pushm[1] Nuprl_font!tneg slot{'P} popm ezone

dform and_df : parens :: "prec"[prec_and] :: "and"{'P1; 'P2} =
   szone pushm[3] slot["lt"]{'P1} hspace Nuprl_font!wedge `" " slot["le"]{'P2} popm ezone

dform or_df : parens :: "prec"[prec_or] :: "or"{'P1; 'P2} =
   szone pushm[3] slot["lt"]{'P1} hspace Nuprl_font!vee `" " slot["le"]{'P2} popm ezone

dform implies_df : parens :: "prec"[prec_implies] :: "implies"{'P1; 'P2} =
   szone pushm[3] slot["le"]{'P1} hspace Nuprl_font!Rightarrow `" " slot["lt"]{'P2} popm ezone

dform all_df1 : parens :: "prec"[prec_quant] :: "all"{'ty} =
   Nuprl_font!forall slot{'ty}

dform all_df2 : parens :: "prec"[prec_quant] :: "all"{'ty; x. 'P} =
   szone pushm[3] Nuprl_font!forall slot{'x} `":" slot{'ty} `"." hspace slot{'P} popm ezone

dform exists_df1 : "exists"{'ty} =
   Nuprl_font!exists slot{'ty}

dform exists_df2 : parens :: "prec"[prec_quant] :: "exists"{'ty; x. 'P} =
   szone pushm[3] Nuprl_font!exists slot{'x} `":" slot{'ty} `"." hspace slot{'P} popm ezone

dform select_df1 : parens :: "prec"[prec_apply] :: select{'ty} =
   Nuprl_font!epsilon slot{'ty}

dform select_df2 : parens :: "prec"[prec_quant] :: select{'ty; x. 'P} =
   szone pushm[3] Nuprl_font!epsilon slot{'x} `":" slot{'ty} `"." hspace slot{'P} popm ezone

(************************************************************************
 * Tests.
 *)
interactive true_wf {| intro [] |} :
   sequent { <H> >- wf } -->
   sequent { <H> >- "true" in bool }

interactive true_intro {| intro [] |} :
   sequent { <H> >- wf } -->
   sequent { <H> >- "true" }

interactive and_wf {| intro [] |} :
   sequent { <H> >- 'P in bool } -->
   sequent { <H> >- 'Q in bool } -->
   sequent { <H> >- ('P & 'Q) in bool }

interactive identity :
   [wf] sequent { <H> >- 'P IN bool } -->
   sequent { <H> >- 'P => 'P }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
