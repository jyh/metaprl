(*
 * Display forms for math mode.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2000 Jason Hickey, Caltech
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
 * jyh@cs.caltech.edu
 *)

include Itt_theory

open Itt_equal
open Itt_rfun
open Itt_logic
open Itt_int_base
open Itt_w

(************************************************************************
 * SETS
 ************************************************************************)

declare math_set
declare math_isset{'s}
declare math_collect{'x; 'T; 'a}
declare math_set_ind{'s; 'T; 'f; 'g; 'b}

dform set_df : math_set =
   i["set"]

dform isset_df1 : mode[tex] :: math_isset{'s} =
   izone `"{" ezone
   slot{'s}
   izone `"\\in {\\it set}}" ezone

dform collect_df1 : mode[tex] :: math_collect{'x; 'T; 'a} =
   izone `"{{\\it collect}(" ezone
   slot{'x}
   izone `"\\in " ezone
   slot{'T}
   izone `"." ezone
   slot{'a}
   izone `")}" ezone

dform set_ind_df1 : mode[tex] :: math_set_ind{'s; 'T; 'f; 'g; 'b} =
   izone `"{{\\it set\\_ind(" ezone
   slot{'s}
   izone `";" ezone
   slot{'T}
   izone `"," ezone
   slot{'f}
   izone `"," ezone
   slot{'g}
   izone `"." ezone
   slot{'b}
   izone `")}" ezone

dform isset_df : except_mode[tex] :: parens :: "prec"[prec_apply] :: math_isset{'s} =
   slot{'s} `" set"

dform collect_df : except_mode[tex] :: parens :: "prec"[prec_apply] :: math_collect{'x; 'T; 'a} =
   szone pushm[3] `"collect" " " slot{'x} `":" " " slot{'T} `"." " " slot{'a} popm ezone

dform set_ind_df : except_mode[tex] :: parens :: "prec"[prec_tree_ind] :: math_set_ind{'z; 'a; 'f; 'g; 'body} =
   szone pushm[3]
   pushm[3] `"let set(" slot{'a} `", " slot{'f} `")." slot{'g} `" =" hspace slot{'z} hspace `"in" popm hspace
   slot{'body} popm ezone

(************************************************************************
 * EQUALITY
 ************************************************************************)

declare math_eq{'s1; 's2}
declare math_equal{'s1; 's2}
declare math_funset{'z; 'f}
declare math_funprop{'z; 'P}
declare math_dfunprop{'x; 'A; 'B}

dform eqinner_df1 : mode[tex] :: math_eq{'s1; 's2} =
   izone `"{{\\it eq}(" ezone
   slot{'s1}
   izone `"," ezone
   slot{'s2}
   izone `")}" ezone

dform eq_df1 : mode[tex] :: math_equal{'s1; 's2} =
   izone `"{{\\it equal}(" ezone
   slot{'s1}
   izone `"," ezone
   slot{'s2}
   izone `")}" ezone

dform funset_df1 : mode[tex] :: math_funset{'z; 'f} =
   izone `"{{\\it fun\\_set}(" ezone
   slot{'z}
   izone `"." ezone
   slot{'f}
   izone `")}" ezone

dform funprop_df1 : mode[tex] :: math_funprop{'z; 'f} =
   izone `"{{\\it fun\\_prop}(" ezone
   slot{'z}
   izone `"." ezone
   slot{'f}
   izone `")}" ezone

dform dfunprop_df1 : mode[tex] :: math_dfunprop{'x; 'z; 'f} =
   izone `"{{\\it dfun\\_prop}(" ezone
   slot{'z}
   izone `"\\colon " ezone
   slot{'z}
   izone `"." ezone
   slot{'f}
   izone `")}" ezone

dform eq_df : except_mode[tex] :: parens :: "prec"[prec_equal] :: math_eq{'s1; 's2} =
   slot{'s1} `" =S " slot{'s2}

dform eq_inner_df : except_mode[tex] :: math_eq{'s1; 's2} =
   slot{'s1} `" =s " slot{'s2}

dform fun_set_df : except_mode[tex] :: parens :: "prec"[prec_apply] :: math_funset{'x; 'P} =
   Nuprl_font!forall slot{'x} `"." slot{'P} `" fun_set"

dform fun_prop_df : except_mode[tex] :: parens :: "prec"[prec_apply] :: math_funprop{'x; 'P} =
   Nuprl_font!forall slot{'x} `"." slot{'P} `" fun_prop"

(************************************************************************
 * MEMBERSHIP
 ************************************************************************)

declare math_mem{'x; 'y}
declare math_member{'x; 'y}

dform mem_df1 : mode[tex] :: math_mem{'s1; 's2} =
   izone `"{" ezone
   slot{'s1}
   izone `"\\in_s " ezone
   slot{'s2}
   izone `"}" ezone

dform member_df1 : mode[tex] :: math_member{'s1; 's2} =
   izone `"{" ezone
   slot{'s1}
   izone `"\\in_S " ezone
   slot{'s2}
   izone `"}" ezone

dform mem_df : except_mode[tex] :: parens :: "prec"[prec_apply] :: math_mem{'x; 't} =
   slot{'x} " " Nuprl_font!member `"s" " " slot{'t}

dform member_df : except_mode[tex] :: parens :: "prec"[prec_apply] :: math_member{'x; 't} =
   slot{'x} " " Nuprl_font!member `"S" " " slot{'t}

(************************************************************************
 * SEPARATION
 ************************************************************************)

declare math_sep{'x; 's; 'P}
declare math_restricted{'P}

dform sep_df1 : mode[tex] :: math_sep{'x; 's; 'P} =
   izone `"{\\left\\{" ezone
   slot{'x}
   izone `"\\in_s " ezone
   slot{'s} `"| " slot{'P}
   izone `"\\right\\}}" ezone

dform restricted_df1 : mode[tex] :: math_restricted{'P} =
   izone `"{{\\it restricted}(" ezone
   slot{'P}
   izone `")}" ezone

dform sep_df : except_mode[tex] :: math_sep{'x; 's; 'P} =
   szone pushm[3] `"{ " slot{'x} " " Nuprl_font!member " " slot{'s} `" |"
   hspace slot{'P} " " `"}" popm ezone

dform restricted_df : except_mode[tex] :: parens :: "prec"[prec_quant] :: math_restricted{'P} =
   slot{'P} `" res"

(************************************************************************
 * LOGIC
 ************************************************************************)

declare math_strue
declare math_sfalse
declare math_sor{'A; 'B}
declare math_sand{'A; 'B}
declare math_simplies{'A; 'B}
declare math_snot{'A}
declare math_siff{'A; 'B}
declare math_sall{'x; 'A; 'B}
declare math_sall{'x; 'A}
declare math_sexists{'x; 'A; 'B}
declare math_sexists{'x; 'A}
declare math_dall{'x; 'A; 'B}
declare math_dexists{'x; 'A; 'B}

dform strue_df1 : mode[tex] :: math_strue =
   izone `"{\\it true}_s " ezone

dform sfalse_df1 : mode[tex] :: math_sfalse =
   izone `"{\\it false}_s " ezone

dform snot_df1 : mode[tex] :: math_snot{'s1} =
   izone `"{\\neg " ezone
   slot{'s1}
   izone `"}" ezone

dform sor_df1 : mode[tex] :: math_sor{'s1; 's2} =
   izone `"{" ezone
   slot{'s1}
   izone `"\\vee_s " ezone
   slot{'s2}
   izone `"}" ezone

dform sand_df1 : mode[tex] :: math_sand{'s1; 's2} =
   izone `"{" ezone
   slot{'s1}
   izone `"\\wedge_s " ezone
   slot{'s2}
   izone `"}" ezone

dform simplies_df1 : mode[tex] :: math_simplies{'s1; 's2} =
   slot{'s1}
   izone `"\\Rightarrow_s " ezone
   slot{'s2}

dform siff_df1 : mode[tex] :: math_siff{'s1; 's2} =
   slot{'s1}
   izone `"\\Leftrightarrow_s " ezone
   slot{'s2}

dform sall_df1 : mode[tex] :: math_sall{'x; 'A; 'B} =
   izone `"\\forall_s " ezone
   slot{'x}
   izone `"\\colon " ezone
   slot{'A}
   izone `"." ezone
   slot{'B}

dform sall_df2 : mode[tex] :: math_sall{'x; 'A} =
   izone `"\\forall_s " ezone
   slot{'x}
   izone `"." ezone
   slot{'A}

dform sexists_df1 : mode[tex] :: math_sexists{'x; 'A; 'B} =
   izone `"\\exists_s " ezone
   slot{'x}
   izone `"\\colon " ezone
   slot{'A}
   izone `"." ezone
   slot{'B}

dform sexists_df2 : mode[tex] :: math_sexists{'x; 'A} =
   izone `"\\exists_s " ezone
   slot{'x}
   izone `"." ezone
   slot{'A}

dform dall_df1 : mode[tex] :: math_dall{'x; 'A; 'B} =
   izone `"\\forall " ezone
   slot{'x}
   izone `"\\in_s " ezone
   slot{'A}
   izone `"." ezone
   slot{'B}

dform dexists_df1 : mode[tex] :: math_dexists{'x; 'A; 'B} =
   izone `"\\exists " ezone
   slot{'x}
   izone `"\\in_s " ezone
   slot{'A}
   izone `"." ezone
   slot{'B}

dform true_df : except_mode[tex] :: except_mode[src] :: math_strue =
   `"True_s"

dform false_df : except_mode[tex] :: except_mode[src] :: math_sfalse =
   `"False_s"

dform not_df1 : except_mode[tex] :: except_mode[src] :: parens :: "prec"[prec_not] :: math_snot{'a} =
   Nuprl_font!tneg slot["le"]{'a}

dform implies_df : except_mode[tex] :: except_mode[src] :: parens :: "prec"[prec_implies] :: math_simplies{'a; 'b} =
   slot["le"]{'a} " " Nuprl_font!Rightarrow " " slot["lt"]{'b}

dform and_df : except_mode[tex] :: except_mode[src] :: parens :: "prec"[prec_and] :: math_sand{'a; 'b} =
   slot["le"]{'a} " " Nuprl_font!wedge " " slot["lt"]{'b}

dform or_df : except_mode[tex] :: except_mode[src] :: parens :: "prec"[prec_or] :: math_sor{'a; 'b} =
   slot["le"]{'a} " " Nuprl_font!vee " " slot["lt"]{'b}

dform iff_df : except_mode[tex] :: except_mode[src] :: parens :: "prec"[prec_iff] :: math_siff{'a; 'b} =
   slot["le"]{'a} " " Nuprl_font!Leftrightarrow " " slot["lt"]{'b}

dform all_df1 : except_mode[tex] :: except_mode[src] :: parens :: "prec"[prec_quant] :: math_sall{'x; 'A; 'B} =
   pushm[3] Nuprl_font!forall slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm

dform exists_df1 : except_mode[tex] :: except_mode[src] :: parens :: "prec"[prec_quant] :: math_sexists{'x; 'A; 'B} =
   pushm[3] Nuprl_font!"exists" slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm

dform all_df2 : except_mode[tex] :: except_mode[src] :: parens :: "prec"[prec_quant] :: math_dall{'x; 'A; 'B} =
   pushm[3] Nuprl_font!forall slot{'x} Nuprl_font!member slot{'A} sbreak["",". "] slot{'B} popm

dform exists_df2 : except_mode[tex] :: except_mode[src] :: parens :: "prec"[prec_quant] :: math_dexists{'x; 'A; 'B} =
   pushm[3] Nuprl_font!"exists" slot{'x} Nuprl_font!member slot{'A} sbreak["",". "] slot{'B} popm

dform all_df3 : except_mode[tex] :: except_mode[src] :: parens :: "prec"[prec_quant] :: math_sall{'x; 'B} =
   pushm[3] Nuprl_font!forall slot{'x} sbreak["",". "] slot{'B} popm

dform exists_df3 : except_mode[tex] :: except_mode[src] :: parens :: "prec"[prec_quant] :: math_sexists{'x; 'B} =
   pushm[3] Nuprl_font!"exists" slot{'x} sbreak["",". "] slot{'B} popm

(************************************************************************
 * EMPTY
 ************************************************************************)

declare math_empty

dform empty_df1 : mode[tex] :: math_empty =
   izone `"{\\{\\}}" ezone

dform empty_df2 : except_mode[tex] :: except_mode[src] :: math_empty =
   `"{}"

(************************************************************************
 * SINGLETON
 ************************************************************************)

declare math_sing{'s}

dform sing_df1 : mode[tex] :: math_sing{'s} =
   izone `"{\\{" ezone
   slot{'s}
   izone `"\\}}" ezone


dform sing_df2 : except_mode[tex] :: math_sing{'s} =
   `"{" slot{'s} `"}"

(************************************************************************
 * UNION
 ************************************************************************)

declare math_union{'s}

dform union_df1 : mode[tex] :: math_union{'s} =
   izone `"{\\bigcup " ezone
   slot{'s}
   izone `"}" ezone

dform union_df2 : mode[tex] :: math_union{'s1; 's2} =
   izone `"{" ezone
   slot{'s1}
   izone `"\\cup " ezone
   slot{'s2}
   izone `"}" ezone

dform union_df3 : except_mode[tex] :: parens :: "prec"[prec_or] :: math_union{'s1; 's2} =
   slot{'s1} " " cup " " slot{'s2}

dform union_df4 : except_mode[tex] :: parens :: "prec"[prec_or] :: math_union{'s} =
   cup " " slot{'s}

(************************************************************************
 * INTERSECTION
 ************************************************************************)

declare math_isect{'s1; 's2}
declare math_isect{'s}

dform isect_df1 : mode[tex] :: math_isect{'s} =
   izone `"{\\bigcap " ezone
   slot{'s}
   izone `"}" ezone

dform isect_df2 : mode[tex] :: math_isect{'s1; 's2} =
   izone `"{" ezone
   slot{'s1}
   izone `"\\cap " ezone
   slot{'s2}
   izone `"}" ezone

dform isect_df3 : except_mode[tex] :: parens :: "prec"[prec_or] :: math_isect{'s1; 's2} =
   slot{'s1} " " cap " " slot{'s2}

dform isect_df4 : except_mode[tex] :: parens :: "prec"[prec_or] :: math_isect{'s} =
   cap " " slot{'s}

(************************************************************************
 * PAIR
 ************************************************************************)

declare math_pair{'s1; 's2}

dform pair_df1 : mode[tex] :: math_pair{'s1; 's2} =
   izone `"{\\left( " ezone
   slot{'s1}
   izone `"," ezone
   slot{'s2}
   izone `"\\right)}" ezone

dform pair_df : except_mode[tex] :: math_pair{'s1; 's2} =
   `"(" pushm[0] szone slot{'s1} `"," hspace slot{'s2} `")" ezone popm

(************************************************************************
 * SUBSET
 ************************************************************************)

declare math_subset{'s1; 's2}

dform pair_df1 : mode[tex] :: math_subset{'s1; 's2} =
   izone `"{" ezone
   slot{'s1}
   izone `"\\subseteq_s " ezone
   slot{'s2}
   izone `"}" ezone

dform subset_df : except_mode[tex] :: math_subset{'s1; 's2} =
   slot{'s1} `" " Nuprl_font!subseteq `"s " slot{'s2}

(************************************************************************
 * INFINITY
 ************************************************************************)

declare math_inf
declare math_zero
declare math_succ{'i}
declare math_lt{'i; 'j}

dform inf_df1 : mode[tex] :: math_inf =
   izone `"\\omega " ezone

dform zero_df1 : mode[tex] :: math_zero =
   izone `"0_s " ezone

dform succ_df1 : mode[tex] :: math_succ{'i} =
   izone `"{s(" ezone
   slot{'i}
   izone `")}" ezone

dform lt_df1 : mode[tex] :: math_lt{'i; 'j} =
   izone `"{" ezone
   slot{'i}
   izone `" <_s " ezone
   slot{'j}
   izone `"}" ezone

dform zero_df2 : except_mode[tex] :: math_zero =
   `"0s"

dform succ_df2 : except_mode[tex] :: math_succ{'i} =
   `"s(" slot{'i} `")"

dform inf_df2 : except_mode[tex] :: math_inf =
   Nuprl_font!mathbbN `"s"

dform lt_df2 : except_mode[tex] :: parens :: "prec"[prec_compare] :: math_lt{'i; 'j} =
   pushm[0] szone slot{'i} `" <" hspace slot{'j} ezone popm

(************************************************************************
 * RELATION
 ************************************************************************)

declare math_rel{'x; 'y; 'P; 's1; 's2}

dform rel_df1 : mode[tex] :: math_rel{'x; 'y; 'P; 's1; 's2} =
   izone `"{{\\mathbb B}(" ezone
   slot{'x}
   izone `"\\in " ezone
   slot{'s1}
   izone `", " ezone
   slot{'y}
   izone `"\\in " ezone
   slot{'s2}
   izone `". " ezone
   slot{'P}
   izone `")}" ezone

dform rel_df : except_mode[tex] :: parens :: "prec"[prec_quant] :: math_rel{'a; 'b; 'P; 's1; 's2} =
   szone pushm[3]
   Nuprl_font!mathbbB slot{'a} " " Nuprl_font!member slot{'s1} `"," hspace
   slot{'b} " " Nuprl_font!member " " slot{'s2} `"." hspace
   slot{'P}
   popm ezone

(************************************************************************
 * SUBSET COLLECTION
 ************************************************************************)

declare math_power{'s1; 's2}

dform power_df1 : mode[tex] :: math_power{'s1; 's2} =
   izone `"{{\\mathbb P}{" ezone
   slot{'s1}
   izone `"\\rightarrow " ezone
   slot{'s1}
   izone `"}}" ezone

dform power_df3 : except_mode[tex] :: math_power{'s1; 's2} =
   mathbbP `"(" pushm[0] szone slot{'s1} `" ->" hspace  slot{'s2} `")" ezone popm

(************************************************************************
 * EQUIVALENCE RELATION
 ************************************************************************)

declare math_equiv{'s; 'r; 'a; 'b}
declare math_equiv{'s; 'r}
declare math_equivfunset{'s; 'r; 'z; 'f}
declare math_equivfunprop{'s; 'r; 'z; 'P}

dform equiv_df1 : mode[tex] :: math_equiv{'s; 'r; 'a; 'b} =
   izone `"{{\\it equiv}(" ezone
   slot{'s}
   izone `"," ezone
   slot{'r}
   izone `"," ezone
   slot{'a}
   izone `"," ezone
   slot{'b}
   izone `")}" ezone

dform equiv_df1 : mode[tex] :: math_equiv{'s1; 's2} =
   izone `"{{\\it equiv}(" ezone
   slot{'s1}
   izone `"," ezone
   slot{'s2}
   izone `")}" ezone

dform equivfunset_df1 : mode[tex] :: math_equivfunset{'s; 'r; 'z; 'f} =
   izone `"{{\\it equiv\\_fun\\_set}(" ezone
   slot{'s}
   izone `"," ezone
   slot{'r}
   izone `"," ezone
   slot{'z}
   izone `"." ezone
   slot{'f}
   izone `")}" ezone

dform equivfunprop_df1 : mode[tex] :: math_equivfunprop{'s; 'r; 'z; 'P} =
   izone `"{{\\it equiv\\_fun\\_prop}(" ezone
   slot{'s}
   izone `"," ezone
   slot{'r}
   izone `"," ezone
   slot{'z}
   izone `"." ezone
   slot{'P}
   izone `")}" ezone

dform equivrl_df : parens :: except_mode[tex] :: math_equiv{'s1; 's2} =
   `"equiv(" slot{'s1} `"; " slot{'s2} `")"

dform equiv__df : parens :: except_mode[tex] :: math_equiv{'s; 'r; 'a; 'b} =
   `"equiv(" slot{'s} `"; " slot{'r} `"; " slot{'a} `"; " slot{'b} `")"

dform equiv_fun_set_df : except_mode[tex] :: parens :: "prec"[prec_apply] :: math_equivfunset{'s; 'r; 'z; 'f} =
   Nuprl_font!forall slot{'z} `"." slot{'f} `" equiv_fun_set"

dform equiv_fun_prop_df : except_mode[tex] :: parens :: "prec"[prec_apply] :: math_equivfunprop{'s; 'r; 'z; 'P} =
   Nuprl_font!forall slot{'z} `"." slot{'P} `" equiv_fun_prop"

(************************************************************************
 * GROUP
 ************************************************************************)

declare math_group{'g}
declare math_car{'g}
declare math_eqG{'g}
declare math_op{'g; 'a; 'b}
declare math_id{'g}
declare math_inv{'g; 'a}

dform group_df1 : mode[tex] :: math_group{'g} =
   izone `"{{\\it group}(" ezone
   slot{'g}
   izone `")}" ezone

dform car_df1 : mode[tex] :: math_car{'g} =
   izone `"{{\\it car}(" ezone
   slot{'g}
   izone `")}" ezone

dform eqG_df1 : mode[tex] :: math_eqG{'g} =
   izone `"{{\\it eqG}(" ezone
   slot{'g}
   izone `")}" ezone

dform id_df1 : mode[tex] :: math_id{'g} =
   izone `"{{\\it id}(" ezone
   slot{'g}
   izone `")}" ezone

dform op_df1 : mode[tex] :: math_op{'g; 'a; 'b} =
   izone `"{{\\it op}(" ezone
   slot{'g}
   izone `"," ezone
   slot{'a}
   izone `"," ezone
   slot{'b}
   izone `")}" ezone

dform inv_df1 : mode[tex] :: math_inv{'g; 'a} =
   izone `"{{\\it inv}(" ezone
   slot{'g}
   izone `"," ezone
   slot{'a}
   izone `")}" ezone

dform group_df : except_mode[tex] :: math_group{'g} =
   slot{'g} `" group"

dform car_df : except_mode[tex] :: math_car{'g} =
   `"car(" slot{'g} `")"

dform eqG_df1 : except_mode[tex] :: math_eqG{'g} =
   `"eqG(" slot{'g} `")"

dform id_df : except_mode[tex] :: math_id{'g} =
   `"id(" slot{'g} `")"

dform op_df : parens :: except_mode[tex] :: math_op{'g; 'a; 'b} =
   `"op(" slot{'g} `"; " slot{'a}  `"; " slot{'b} `")"

dform inv_df : parens :: except_mode[tex] :: math_inv{'g; 'a} =
   `"inv(" slot{'g} `"; " slot{'a} `")"

(************************************************************************
 * GROUP BUILDER
 ************************************************************************)

declare math_groupbvd{'h; 'g; 's}

dform group_bvd_df1 : mode[tex] :: math_groupbvd{'h; 'g; 's} =
   izone `"{{\\it group\\_bvd}(" ezone
   slot{'h}
   izone `"," ezone
   slot{'g}
   izone `"," ezone
   slot{'s}
   izone `")}" ezone

dform group_bvd_df : parens :: except_mode[tex] :: math_groupbvd{'h; 'g; 's} =
   `"group_builder(" slot{'h} `"; " slot{'g} `"; " slot{'s} `")"

(************************************************************************
 * ABELIAN GROUP
 ************************************************************************)

declare math_abel{'g}

dform abel_df1 : mode[tex] :: math_abel{'g} =
   izone `"{{\\it abel}(" ezone
   slot{'g}
   izone `")}" ezone

dform abel_df : except_mode[tex] :: math_abel{'g} =
   `"abel(" slot{'g} `")"

(************************************************************************
 * SUBGROUP
 ************************************************************************)

declare math_subgroup{'s; 'g}

dform subgroup_df1 : mode[tex] :: math_subgroup{'s; 'g} =
   izone `"{{\\it subgroup}(" ezone
   slot{'s}
   izone `"," ezone
   slot{'g}
   izone `")}" ezone

dform subgroup_df : except_mode[tex] :: math_subgroup{'s; 'g} =
   `"subgroup(" slot{'s} `"; " slot{'g} `")"

(************************************************************************
 * CYCLIC SUBGROUP
 ************************************************************************)

declare math_power{'g; 'z; 'n}
declare math_cycsubg{'s; 'g; 'a}

dform power_df1 : mode[tex] :: math_power{'g; 'z; 'n} =
   izone `"{{\\it power}(" ezone
   slot{'g}
   izone `"," ezone
   slot{'z}
   izone `"," ezone
   slot{'n}
   izone `")}" ezone

dform cycsubg_df1 : mode[tex] :: math_cycsubg{'s; 'g; 'a} =
   izone `"{{\\it cyclic\\_subgroup}(" ezone
   slot{'s}
   izone `"," ezone
   slot{'g}
   izone `"," ezone
   slot{'a}
   izone `")}" ezone

dform power_df : parens :: except_mode[tex] :: math_power{'g; 'z; 'n} =
   `"power(" slot{'g} `"; " slot{'z}  `"; " slot{'n} `")"

dform cycsubg_df : except_mode[tex] :: math_cycsubg{'s; 'g; 'a} =
   `"cyclic_subgroup(" slot{'s} `"; " slot{'g} `"; " slot{'a} `")"

(************************************************************************
 * CYCLIC GROUP
 ************************************************************************)

declare math_cycgroup{'g; 'a}

dform cycgroup_df1 : mode[tex] :: math_cycgroup{'g; 'a} =
   izone `"{{\\it cyclic\\_group}(" ezone
   slot{'g}
   izone `"," ezone
   slot{'a}
   izone `")}" ezone

dform cycgroup_df : except_mode[tex] :: math_cycgroup{'g; 'a} =
   `"cyclic_group(" slot{'g} `"; " slot{'a} `")"

(************************************************************************
 * COSET
 ************************************************************************)

declare math_lcoset{'h; 'g; 'a}
declare math_rcoset{'h; 'g; 'a}

dform lcoset_df1 : mode[tex] :: math_lcoset{'h; 'g; 'a} =
   izone `"{{\\it left\\_coset}(" ezone
   slot{'h}
   izone `"," ezone
   slot{'g}
   izone `"," ezone
   slot{'a}
   izone `")}" ezone

dform rcoset_df1 : mode[tex] :: math_rcoset{'h; 'g; 'a} =
   izone `"{{\\it right\\_coset}(" ezone
   slot{'h}
   izone `"," ezone
   slot{'g}
   izone `"," ezone
   slot{'a}
   izone `")}" ezone

dform lcoset_df : parens :: except_mode[tex] :: math_lcoset{'h; 'g; 'a} =
   `"lcoset(" slot{'h} `"; " slot{'g} `"; " slot{'a} `")"

dform rcoset_df : parens :: except_mode[tex] :: math_rcoset{'h; 'g; 'a} =
   `"rcoset(" slot{'h} `"; " slot{'g} `"; " slot{'a} `")"

(************************************************************************
 * NORMAL SUBGROUP
 ************************************************************************)

declare math_normalsubg{'s; 'g}

dform normalsubg_df1 : mode[tex] :: math_normalsubg{'s; 'g} =
   izone `"{{\\it normal\\_subgroup}(" ezone
   slot{'s}
   izone `"," ezone
   slot{'g}
   izone `")}" ezone

dform normalsubg_df : except_mode[tex] :: math_normalsubg{'s; 'g} =
   `"normal_subgroup(" slot{'s} `"; " slot{'g} `")"

(************************************************************************
 * SET BUILDER
 ************************************************************************)

declare math_setbvd{'x; 's; 'a}

dform set_bvd_df1 : mode[tex] :: math_setbvd{'x; 's; 'a} =
   izone `"{\\left\\{" ezone
   slot{'a} `"| " 
   slot{'x}
   izone `"\\in_s " ezone
   slot{'s}
   izone `"\\right\\}}" ezone

dform set_bvd_df : parens :: except_mode[tex] :: math_setbvd{'x; 's; 'a} =
   pushm[0] `"{" slot{'a} mid slot{'x} " " Nuprl_font!member `"s " slot{'s} `"}" popm

(************************************************************************
 * INVERSE IMAGE
 ************************************************************************)

declare math_invimage{'x; 's; 'a; 't}

dform inv_image_df1 : mode[tex] :: math_invimage{'x; 's; 'a; 't} =
   izone `"{\\left\\{" ezone
   slot{'x}
   izone `"\\in_s " ezone
   slot{'s} `"| " 
   slot{'a}
   izone `"\\in_s " ezone
   slot{'t}
   izone `"\\right\\}}" ezone

dform inv_image_df : parens :: except_mode[tex] :: math_invimage{'x; 's; 'a; 't} =
   pushm[0] `"{" slot{'x} " " Nuprl_font!member `"s " slot{'s} mid slot{'a} " " Nuprl_font!member `"s " slot{'t} `"}" popm

(************************************************************************
 * HOMOMORPHISM
 ************************************************************************)

declare math_hom{'x; 'g1; 'g2; 'f}

dform hom_df1 : mode[tex] :: math_hom{'x; 'g1; 'g2; 'f} =
   izone `"{{\\it homomorphism}(" ezone
   slot{'f}
   izone `":" ezone
   slot{'g1}
   izone `"->" ezone
   slot{'g2}
   izone `")}" ezone

dform hom_df : parens :: except_mode[tex] :: math_hom{'x; 'g1; 'g2; 'f} =
   `"hom(" slot{'g1} `"; " slot{'g2} `"; " slot{'f} `")"

(************************************************************************
 * KERNEL
 ************************************************************************)

declare math_ker{'x; 'h; 'g1; 'g2; 'f}

dform ker_df1 : mode[tex] :: math_ker{'x; 'h; 'g1; 'g2; 'f} =
   izone `"{{\\it kernel}(" ezone
   slot{'h}
   izone `"," ezone
   slot{'g1}
   izone `"," ezone
   slot{'g2}
   izone `"," ezone
   slot{'x}
   izone `"." ezone
   slot{'f}
   izone `")}" ezone

dform ker_df : parens :: except_mode[tex] :: math_ker{'x; 'h; 'g1; 'g2; 'f} =
   `"ker(" slot{'h} `"; " slot{'g1} `"; " slot{'g2} `"; " slot{'f} `")"

(************************************************************************
 * ISOMORPHISM
 ************************************************************************)

declare math_iso{'x; 'g1; 'g2; 'f}

dform iso_df1 : mode[tex] :: math_iso{'x; 'g1; 'g2; 'f} =
   izone `"{{\\it isomorphism}(" ezone
   slot{'f}
   izone `":" ezone
   slot{'g1}
   izone `"->" ezone
   slot{'g2}
   izone `")}" ezone
(*   izone `"{{\\it iso}(" ezone
   slot{'g1}
   izone `"," ezone
   slot{'g2}
   izone `"," ezone
   slot{'x}
   izone `"." ezone
   slot{'f}
   izone `")}" ezone
*)
dform iso_df : parens :: except_mode[tex] :: math_iso{'x; 'g1; 'g2; 'f} =
   `"iso(" slot{'g1} `"; " slot{'g2} `"; " slot{'f} `")"

(************************************************************************
 * KLEIN 4-GROUP
 ************************************************************************)

declare math_klein4
declare math_k0
declare math_k1
declare math_k2
declare math_k3

dform klein4_df1 : mode[tex] :: math_klein4 =
   izone `"{{\\it klein4}}" ezone

dform k0_df1 : mode[tex] :: math_k0 =
   izone `"{{\\it k0}}" ezone

dform k1_df1 : mode[tex] :: math_k1 =
   izone `"{{\\it k1}}" ezone

dform k2_df1 : mode[tex] :: math_k2 =
   izone `"{{\\it k2}}" ezone

dform k3_df1 : mode[tex] :: math_k3 =
   izone `"{{\\it k3}}" ezone

dform klein4_df : except_mode[tex] :: math_klein4 =
   `"klein4"

dform k0_df : except_mode[tex] :: math_k0 =
   `"k0"

dform k1_df : except_mode[tex] :: math_k1 =
   `"k1"

dform k2_df : except_mode[tex] :: math_k2 =
   `"k2"

dform k3_df : except_mode[tex] :: math_k3 =
   `"k3"

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
