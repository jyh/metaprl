doc <:doc< 
   @begin[doc]
   @module[Itt_comment]
   
   Terms used for comments in the @Nuprl type theory.
   @end[doc]
   
   ----------------------------------------------------------------
   
   @begin[license]
   Copyright (C) 2000 Jason Hickey, Caltech
   
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
   
   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]
>>

extends Base_theory

(************************************************************************
 * UNIVERSES AND EQUALITY
 ************************************************************************)

declare math_type{'a}
declare math_univ{'i}
declare math_equal{'T; 'a; 'b}
declare math_member{'T; 'a}
declare math_cumulativity{'i; 'j}

prec prec_type
prec prec_equal

(************************************************
 * TeX mode.
 *)
dform math_type_df1 : mode[tex] :: math_type{'t} =
   slot{'t}
   izone `"\\,\\mathtt{" ezone
   `"Type"
   izone "}" ezone

dform math_univ_df : mode[tex] :: math_univ{'i} =
   izone `"{\\mathbb U}_{" ezone
   slot{'i}
   izone `"}" ezone

dform math_equal_df1 : mode[tex] :: math_equal{'T; 'a; 'b} =
   izone `"{" ezone
   slot{'a}
   izone `" = " ezone
   slot{'b}
   izone `" \\in " ezone
   slot{'T}
   izone `"}" ezone

dform math_member_df1 : mode[tex] :: math_member{'T; 'a} =
   izone `"{" ezone
   slot{'a}
   izone `" \\in " ezone
   slot{'T}
   izone `"}" ezone

dform math_cumulativity_df1 : mode[tex] :: math_cumulativity{'i; 'j} =
   izone `"{{\\it cumulativity}[" ezone
   slot{'i}
   izone `", " ezone
   slot{'j}
   izone `"]}" ezone

(************************************************
 * Normal mode.
 *)

dform equal_df : except_mode[tex] :: parens :: "prec"[prec_equal] :: math_equal{'T; 'a; 'b} =
   szone pushm slot{'a} space `"= " slot{'b} space Nuprl_font!member `" " slot{'T} popm ezone

dform member_df2 : mode[tex] :: parens :: "prec"[prec_equal] :: math_member{'T; 'a} =
   szone pushm slot{'a} space `"IN" hspace slot{'T} popm ezone

dform type_df1 : except_mode[tex] :: parens :: "prec"[prec_type] :: math_type{'a} =
   slot{'a} " " `"Type"

dform univ_df1 : except_mode[tex] :: math_univ{'i} =
   mathbbU `"[" slot{'i} `"]"

dform cumulativity_df : except_mode[tex] :: math_cumulativity{'i; 'j} =
   `"cumulativity[" slot{'i} `";" slot{'j} `"]"

(************************************************************************
 * VOID
 ************************************************************************)

declare math_void
declare math_false

dform math_Void_df1 : math_void =
   math_i["Void"]

dform math_False_df1 : mode[tex] :: math_false =
   izone `"{\\bot}" ezone

dform math_False_df2 : except_mode[tex] :: math_false =
   it["False"]

(************************************************************************
 * UNIT
 ************************************************************************)

declare math_unit
declare math_true
declare math_it

dform math_Unit_df1 : math_unit =
   math_i["Unit"]

dform math_True_df1 : mode[tex] :: math_true =
   izone `"{\\top}" ezone

dform math_True_df2 : except_mode[tex] :: math_true =
   it["True"]

dform math_it_df1 : mode[tex] :: math_it =
   izone `"\\cdot " ezone

dform math_it_df2 : except_mode[tex] :: math_it =
   Nuprl_font!cdot

(************************************************************************
 * ATOM
 ************************************************************************)

declare math_atom
declare math_token{'t}

dform math_Atom_df1 : math_atom =
   math_i["Atom"]

dform math_token_df1 : math_token{'t} =
   math_i["token"] `"(" slot{'t} `")"

(************************************************************************
 * BOOL
 ************************************************************************)

declare math_bool
declare math_btrue
declare math_bfalse
declare math_bor{'a; 'b}
declare math_band{'a; 'b}
declare math_bimplies{'a; 'b}
declare math_bnot{'a}
declare math_assert{'t}
declare math_if{'a; 'b; 'c}

dform math_Bool_df1 : math_bool =
   math_i["Bool"]

dform math_btrue_df1 : math_btrue =
   math_i["tt"]

dform math_bfalse_df1 : math_bfalse =
   math_i["ff"]

(************************************************
 * TeX mode
 *)
dform math_bor_df1 : mode[tex] :: math_bor{'a; 'b} =
   izone `"{" ezone
   slot{'a}
   izone `"\\vee_b " ezone
   slot{'b}
   izone `"}" ezone

dform math_band_df1 : mode[tex] :: math_band{'a; 'b} =
   izone `"{" ezone
   slot{'a}
   izone `"\\wedge_b " ezone
   slot{'b}
   izone `"}" ezone

dform math_bimplies_df1 : mode[tex] :: math_bimplies{'a; 'b} =
   izone `"{" ezone
   slot{'a}
   izone `"\\Rightarrow_b " ezone
   slot{'b}
   izone `"}" ezone

dform math_bnot_df1 : mode[tex] :: math_bnot{'a} =
   izone `"{\\neg_b " ezone
   slot{'a}
   izone `"}" ezone

dform math_assert_df1 : mode[tex] :: math_assert{'a} =
   izone `"{\\uparrow " ezone
   slot{'a}
   izone `"}" ezone

dform math_if_df1 : mode[tex] :: math_if{'a; 'b; 'c} =
   izone `"\\mathop{\\bf if}" ezone
   szone{'a}
   izone `"\\mathrel{\\bf then}" ezone
   szone{'b}
   izone `"\\mathrel{\\bf else}" ezone
   szone{'c}

(************************************************
 * Normal mode.
 *)
prec prec_bimplies
prec prec_bor
prec prec_band
prec prec_bnot
prec prec_assert

prec prec_bimplies < prec_bor
prec prec_bor < prec_band
prec prec_band < prec_bnot
prec prec_bnot < prec_assert

dform bor_df : parens :: "prec"[prec_bor] :: except_mode[tex] :: math_bor{'a; 'b} =
   slot{'a} " " vee subb " " slot{'b}

dform band_df : parens :: "prec"[prec_band] :: except_mode[tex] :: math_band{'a; 'b} =
   slot{'a} " " wedge subb " " slot{'b}

dform bimplies_df : parens :: "prec"[prec_bimplies] :: except_mode[tex] :: math_bimplies{'a; 'b} =
   slot{'a} " " Rightarrow subb " " slot{'b}

dform bnot_df : parens :: "prec"[prec_bnot] :: except_mode[tex] :: math_bnot{'a} =
   tneg subb slot{'a}

dform ifthenelse_df : parens :: "prec"[prec_bor] :: except_mode[tex] :: math_if{'e1; 'e2; 'e3} =
   szone pushm[0] pushm[3] `"if" `" " szone{'e1} `" " `"then" hspace
   szone{'e2} popm hspace
   pushm[3] `"else" hspace szone{'e3} popm popm ezone

dform assert_df : parens :: "prec"[prec_assert] :: except_mode[tex] :: math_assert{'t} =
   downarrow slot{'t}

(************************************************************************
 * INTEGERS
 ************************************************************************)

declare math_int
declare math_number{'n}
declare math_ind{'i; 'm; 'z; 'down; 'base; 'm; 'z; 'up}
declare math_add{'a; 'b}
declare math_sub{'a; 'b}
declare math_mul{'a; 'b}
declare math_div{'a; 'b}
declare math_rem{'a; 'b}
declare math_lt{'a; 'b}
declare math_le{'a; 'b}
declare math_ge{'a; 'b}
declare math_gt{'a; 'b}

dform math_int_df1 : mode[tex] :: math_int =
   izone `"{\\mathbb Z}" ezone

dform math_number_df1 : mode[tex] :: math_number{'i} =
   izone `"{{\\it number}[" ezone
   slot{'i}
   izone `"]}" ezone

dform math_ind_df1 : mode[tex] :: math_ind{'i; 'a; 'b; 'down; 'base; 'c; 'd; 'up} =
   izone `"{{\\it ind}(" ezone
   slot{'i}
   izone `"; " ezone
   slot{'a}
   izone `", " ezone
   slot{'b}
   izone `". " ezone
   slot{'down}
   izone `"; " ezone
   slot{'base}
   izone `"; " ezone
   slot{'c}
   izone `", " ezone
   slot{'c}
   izone `". " ezone
   slot{'up}
   izone `")}" ezone

dform math_add_df1 : mode[tex] :: math_add{'i; 'j} =
   izone `"{" ezone
   slot{'i}
   izone `"+" ezone
   slot{'j}
   izone `"}" ezone

dform math_sub_df1 : mode[tex] :: math_sub{'i; 'j} =
   izone `"{" ezone
   slot{'i}
   izone `"-" ezone
   slot{'j}
   izone `"}" ezone

dform math_mul_df1 : mode[tex] :: math_mul{'i; 'j} =
   izone `"{" ezone
   slot{'i}
   izone `"*" ezone
   slot{'j}
   izone `"}" ezone

dform math_div_df1 : mode[tex] :: math_div{'i; 'j} =
   izone `"{" ezone
   slot{'i}
   izone `"/" ezone
   slot{'j}
   izone `"}" ezone

dform math_rem_df1 : mode[tex] :: math_rem{'i; 'j} =
   izone `"{" ezone
   slot{'i}
   izone `"\\mathrel{\\bf rem}" ezone
   slot{'j}
   izone `"}" ezone

dform math_gt_df1 : mode[tex] :: math_gt{'i; 'j} =
   izone `"{" ezone
   slot{'i}
   izone `">" ezone
   slot{'j}
   izone `"}" ezone

dform math_ge_df1 : mode[tex] :: math_ge{'i; 'j} =
   izone `"{" ezone
   slot{'i}
   izone `"\\ge " ezone
   slot{'j}
   izone `"}" ezone

dform math_lt_df1 : mode[tex] :: math_lt{'i; 'j} =
   izone `"{" ezone
   slot{'i}
   izone `"<" ezone
   slot{'j}
   izone `"}" ezone

dform math_le_df1 : mode[tex] :: math_le{'i; 'j} =
   izone `"{" ezone
   slot{'i}
   izone `"\\le " ezone
   slot{'j}
   izone `"}" ezone

(************************************************
 * Normal mode
 *)

prec prec_compare
prec prec_add
prec prec_mul

dform int_prl_df : except_mode[src] :: math_int = mathbbZ

dform number_df : except_mode[tex] :: math_number{'n} =
   slot{'n}

dform add_df1 : except_mode[tex] :: parens :: "prec"[prec_add] :: math_add{'a; 'b} =
   slot["le"]{'a} `" + " slot["lt"]{'b}

dform sub_df1 : except_mode[tex] :: parens :: "prec"[prec_add] :: math_sub{'a; 'b} =
   slot["lt"]{'a} `" - " slot["le"]{'b}

dform mul_df1 : except_mode[tex] :: parens :: "prec"[prec_mul] :: math_mul{'a; 'b} =
   slot["lt"]{'a} `" * " slot["le"]{'b}

dform div_df1 : except_mode[tex] :: parens :: "prec"[prec_mul] :: math_div{'a; 'b} =
   slot["lt"]{'a} Nuprl_font!"div" slot["le"]{'b}

dform rem_df1 : except_mode[tex] :: parens :: "prec"[prec_mul] :: math_rem{'a; 'b} =
   slot["lt"]{'a} `" % " slot["le"]{'b}

dform lt_df1 : except_mode[tex] :: parens :: "prec"[prec_compare] :: math_lt{'a; 'b} =
   slot["lt"]{'a} `" < " slot["le"]{'b}

dform le_df1 : except_mode[tex] :: parens :: "prec"[prec_compare] :: math_le{'a; 'b} =
   slot["lt"]{'a} Nuprl_font!le slot["le"]{'b}

dform ge_df1 : except_mode[tex] :: parens :: "prec"[prec_compare] :: math_ge{'a; 'b} =
   slot["lt"]{'a} Nuprl_font!ge slot["le"]{'b}

dform gt_df1 : except_mode[tex] :: parens :: "prec"[prec_compare] :: math_gt{'a; 'b} =
   slot["lt"]{'a} `" > " slot["le"]{'b}

(************************************************************************
 * UNION
 ************************************************************************)

declare math_union{'A; 'B}
declare math_inl{'x}
declare math_inr{'x}
declare math_decide{'x; 'y; 'a; 'z; 'b}
declare math_or{'a; 'b}
declare math_cor{'a; 'b}

(************************************************
 * TeX mode
 *)
dform math_union_df1 : mode[tex] :: math_union{'A; 'B} =
   izone `"{" ezone
   slot{'A}
   izone `"+" ezone
   slot{'B}
   izone `"}" ezone

dform math_inl_df1 : mode[tex] :: math_inl{'x} =
   izone `"{{\\it inl}(" ezone
   slot{'x}
   izone `")}" ezone

dform math_inr_df1 : mode[tex] :: math_inr{'x} =
   izone `"{{\\it inr}(" ezone
   slot{'x}
   izone `")}" ezone

dform math_decide_df1 : mode[tex] :: math_decide{'x; 'y; 'a; 'z; 'b} =
   izone `"{\\mathop{\\bf match}" ezone
   slot{'x}
   izone `"\\mathrel{\\bf with}" ezone
   math_inl{'y}
   izone `"\\rightarrow " ezone
   slot{'a} `"|" math_inr{'z}
   izone `"\\rightarrow " ezone
   slot{'b}
   izone `"}" ezone

dform math_or_df1 : mode[tex] :: math_or{'a; 'b} =
   izone `"{" ezone
   slot{'a}
   izone `"\\vee " ezone
   slot{'b}
   izone `"}" ezone

dform math_cor_df1 : mode[tex] :: math_cor{'a; 'b} =
   izone `"{" ezone
   slot{'a}
   izone `"\\vee_c " ezone
   slot{'b}
   izone `"}" ezone

(************************************************
 * Normal display.
 *)
prec prec_inl
prec prec_union
prec prec_or

dform union_df : except_mode[tex] :: parens :: "prec"[prec_union] :: math_union{'A; 'B} =
   slot{'A} " " `"+" " " slot{'B}

dform inl_df : except_mode[tex] :: parens :: "prec"[prec_inl] :: math_inl{'a} =
   `"inl" " " slot{'a}

dform inr_df : except_mode[tex] :: parens :: "prec"[prec_inl] :: math_inr{'a} =
   `"inr" " " slot{'a}

dform decide_df : except_mode[tex] :: math_decide{'x; 'y; 'a; 'z; 'b} =
   szone pushm[0] pushm[3] `"match" " " slot{'x} " " `"with" hspace
   `"inl " slot{'y} `" -> " slot{'a} popm hspace
   pushm[3] `" | inr " slot{'z} `" -> " slot{'b} popm popm ezone

declare or_df{'a}

dform or_df1 : parens :: "prec"[prec_or] :: math_or{'a; 'b} =
   szone pushm[0] slot["le"]{'a} or_df{'b} popm ezone

dform or_df2 : or_df{math_or{'a; 'b}} =
   or_df{'a} or_df{'b}

dform or_df3 : or_df{'a} =
   hspace Nuprl_font!vee " " slot{'a}

declare cor_df{'a}

dform cor_df1 : except_mode[tex] :: parens :: "prec"[prec_or] :: math_cor{'a; 'b} =
   szone pushm[0] slot["le"]{'a} cor_df{'b} popm ezone

dform cor_df2 : cor_df{math_cor{'a; 'b}} =
   cor_df{'a} cor_df{'b}

dform cor_df3 : cor_df{'a} =
   hspace Nuprl_font!vee `"c" " " slot{'a}

(************************************************************************
 * FUNCTIONS
 ************************************************************************)

declare math_rfun{'f; 'x; 'A; 'B}
declare math_fun{'x; 'A; 'B}
declare math_fun{'A; 'B}
declare math_lambda{'v; 'b}
declare math_apply{'f; 'a}
declare math_well_founded{'A; 'x; 'y; 'R}
declare math_well_founded_assum{'A; 'a1; 'a2; 'R; 'P}
declare math_well_founded_prop{'A}
declare math_well_founded_apply{'P; 'a}
declare math_fix{'f; 'b}

declare math_all{'x; 'A; 'B}
declare math_implies{'A; 'B}
declare math_iff{'A; 'B}
declare math_not{'A}

(************************************************
 * TeX mode
 *)
dform math_rfun_df1 : mode[tex] :: math_rfun{'f; 'x; 'A; 'B} =
   izone `"\\left\\{" ezone
   'f `"|" 'x
   izone `"\\colon " ezone
   'A
   izone `"\\rightarrow " ezone
   'B
   izone `"\\right\\}" ezone

dform math_dfun_df1 : mode[tex] :: math_fun{'x; 'A; 'B} =
   'x
   izone `"\\colon " ezone
   'A
   izone `"\\rightarrow " ezone
   'B

dform math_fun_df1 : mode[tex] :: math_fun{'A; 'B} =
   'A
   izone `"\\rightarrow " ezone
   'B

dform math_lambda_df1 : mode[tex] :: math_lambda{'v; 'b} =
   izone `"\\lambda " ezone
   'v
   izone `"." ezone
   'b

dform math_lambda_df1 : mode[tex] :: math_lambda =
   izone `"\\lambda " ezone

dform math_apply_df1 : mode[tex] :: math_apply{'f; 'a} =
   'f
   izone `"\\ " ezone
   'a

dform math_well_founded_df1 : mode[tex] :: math_well_founded{'A; 'x; 'y; 'R} =
   izone `"{{\\it well\\_founded}(" ezone
   'A
   izone `";" ezone
   'x
   izone `"," ezone
   'y
   izone `"." ezone
   'R
   izone `")}" ezone

dform math_well_founded_assum_df1 : mode[tex] :: math_well_founded_assum{'A; 'x; 'y; 'R; 'P} =
   izone `"{{\\it well\\_founded\\_assum}(" ezone
   'A
   izone `";" ezone
   'x
   izone `"," ezone
   'y
   izone `"." ezone
   'R
   izone `";" ezone
   'P
   izone `")}" ezone

dform math_well_founded_prop_df1 : mode[tex] :: math_well_founded_prop{'P} =
   izone `"{{\\it well\\_founded\\_prop}(" ezone
   'P
   izone `")}" ezone

dform math_well_founded_apply_df1 : mode[tex] :: math_well_founded_apply{'P; 'a} =
   izone `"{{\\it well\\_founded\\_apply}(" ezone
   'P
   izone `";" ezone
   'a
   izone `")}" ezone

dform math_fix_df1 : mode[tex] :: math_fix{'f; 'b} =
   izone `"{{\\it fix}(" ezone
   'f
   izone `"." ezone
   'b
   izone `")}" ezone

dform math_all_df1 : mode[tex] :: math_all{'x; 'A; 'B} =
   izone `"{\\forall " ezone
   'x
   izone `"\\colon " ezone
   'A
   izone `"." ezone
   'B
   izone `"}" ezone

dform math_implies_df1 : mode[tex] :: math_implies{'A; 'B} =
   izone `"{" ezone
   'A
   izone `"\\Rightarrow " ezone
   'B
   izone `"}" ezone

dform math_iff_df1 : mode[tex] :: math_iff{'A; 'B} =
   izone `"{" ezone
   'A
   izone `"\\Leftrightarrow " ezone
   'B
   izone `"}" ezone

dform math_not_df1 : mode[tex] :: math_not{'A} =
   izone `"{\\neg " ezone
   'A
   izone `"}" ezone

(************************************************
 * Normal mode.
 *)
prec prec_fun
prec prec_apply
prec prec_lambda
prec prec_lambda < prec_apply
prec prec_fun < prec_apply
prec prec_fun < prec_lambda

prec prec_not
prec prec_quant
prec prec_iff
prec prec_implies

dform fun_df1 : parens :: "prec"[prec_fun] :: except_mode[tex] :: math_fun{'A; 'B} =
   slot["le"]{'A} " " rightarrow " " slot["lt"]{'B}

dform fun_df2 : parens :: "prec"[prec_fun] :: except_mode[tex] :: math_fun{'x; 'A; 'B} =
   slot{bvar{'x}} `":" slot{'A} " " rightarrow " " slot{'B}

dform fun_df3 : except_mode[tex] :: math_rfun{'f; 'x; 'A; 'B} =
   "{" " " slot{bvar{'f}} mid math_fun{'x; 'A; 'B} `" }"

dform apply_df1 : parens :: "prec"[prec_apply] :: except_mode[tex] :: math_apply{'f; 'a} =
   slot["lt"]{'f} " " slot["le"]{'a}

dform lambda_df1 : parens :: "prec"[prec_lambda] :: except_mode[tex] :: math_lambda{'x; 'b} =
   Nuprl_font!lambda slot{'x} `"." slot{'b}

dform fix_df1 : except_mode[tex] :: except_mode[tex] :: math_fix{'f; 'b} =
   `"fix" `"(" slot{'f} `"." slot{'b} `")"

dform well_founded_prop_df : except_mode[tex] :: except_mode[tex] :: math_well_founded_prop{'A} =
   `"WellFounded " slot{'A} " " rightarrow `" Prop"

dform well_founded_apply_df : except_mode[tex] :: except_mode[tex] :: math_well_founded_apply{'P; 'a} =
   slot{'P} `"[" slot{'a} `"]"

dform well_founded_assum_df : except_mode[tex] :: except_mode[tex] :: math_well_founded_assum{'A; 'a1; 'a2; 'R; 'P} =
   szone pushm[3] `"WellFounded " Nuprl_font!forall slot{'a2} `":" slot{'A} `"."
   `"(" Nuprl_font!forall slot{'a1} `":" slot{'A} `". " slot{'R} " " Rightarrow math_well_founded_apply{'P; 'a1} `")"
   Rightarrow math_well_founded_apply{'P; 'a2} popm ezone

dform well_founded_df : except_mode[tex] :: except_mode[tex] :: math_well_founded{'A; 'a; 'b; 'R} =
   szone pushm[3] `"WellFounded " slot{'a} `"," slot{'b} `":" slot{'A} `"." slot{'R} popm ezone

(*
 * Quantifiers.
 *)
dform not_df1 : except_mode[tex] :: parens :: "prec"[prec_not] :: math_not{'a} =
   Nuprl_font!tneg slot["le"]{'a}

dform implies_df : except_mode[tex] :: parens :: "prec"[prec_implies] :: math_implies{'a; 'b} =
   slot["le"]{'a} " " Nuprl_font!Rightarrow " " slot["lt"]{'b}

dform iff_df : except_mode[tex] :: parens :: "prec"[prec_iff] :: math_iff{'a; 'b} =
   slot["le"]{'a} " " Nuprl_font!Leftrightarrow " " slot["lt"]{'b}

dform all_df1 : except_mode[tex] :: parens :: "prec"[prec_quant] :: except_mode[tex] :: math_all{'x; 'A; 'B} =
   pushm[3] Nuprl_font!forall slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm

(************************************************************************
 * PRODUCT
 ************************************************************************)

declare math_prod{'x; 'A; 'B}
declare math_prod{'A; 'B}
declare math_pair{'a; 'b}
declare math_spread{'e; 'u; 'v; 'b}
declare math_fst{'e}
declare math_snd{'e}
declare math_and{'a; 'b}
declare math_cand{'a; 'b}
declare math_exists{'x; 'A; 'B}

(************************************************
 * TeX mode.
 *)
dform math_prod_df1 : mode[tex] :: math_prod{'x; 'A; 'B} =
   izone `"{" ezone
   slot{'x}
   izone `"\\colon " ezone
   slot{'A}
   izone `"\\times " ezone
   slot{'B}
   izone `"}" ezone

dform math_prod_df2 : mode[tex] :: math_prod{'A; 'B} =
   izone `"{" ezone
   slot{'A}
   izone `"\\times " ezone
   slot{'B}
   izone `"}" ezone

dform math_pair_df1 : mode[tex] :: math_pair{'a; 'b} =
   izone `"{(" ezone
   slot{'a}
   izone `", " ezone
   slot{'b}
   izone `")}" ezone

dform math_spread_df1 : mode[tex] :: math_spread{'e; 'u; 'v; 'b} =
   izone `"{\\mathop{{\\bf match}}" ezone
   slot{'e}
   izone `"\\mathrel{{\\bf with}}" ezone
   math_pair{'u; 'v}
   izone `"\\rightarrow " ezone
   slot{'b}
   izone `"}" ezone

dform math_fst_df1 : mode[tex] :: math_fst{'e} =
   izone `"{{\\it fst}(" ezone
   slot{'e}
   izone `")}" ezone

dform math_snd_df1 : mode[tex] :: math_snd{'e} =
   izone `"{{\\it snd}(" ezone
   slot{'e}
   izone `")}" ezone

dform math_and_df1 : mode[tex] :: math_and{'a; 'b} =
   izone `"{" ezone
   slot{'a}
   izone `"\\wedge " ezone
   slot{'b}
   izone `"}" ezone

dform math_cand_df1 : mode[tex] :: math_cand{'a; 'b} =
   izone `"{" ezone
   slot{'a}
   izone `"\\wedge_c " ezone
   slot{'b}
   izone `"}" ezone

dform math_exists_df1 : mode[tex] :: math_exists{'x; 'A; 'B} =
   izone `"{\\exists " ezone
   slot{'x}
   izone `"\\colon " ezone
   slot{'A}
   izone `"." ezone
   slot{'B}
   izone `"}" ezone

dform math_exists_df1 : mode[tex] :: math_exists =
   izone `"\\exists " ezone

(************************************************
 * NORMAL MODE
 *)
prec prec_prod
prec prec_spread
prec prec_and

prec prec_implies < prec_iff
prec prec_iff < prec_or
prec prec_or < prec_and
prec prec_and < prec_not
prec prec_quant < prec_iff

dform prod_df : parens :: "prec"[prec_prod] :: except_mode[tex] :: math_prod{'A; 'B} =
   pushm[0] slot{'A} " " times " " slot{'B} popm

dform prod_df2 :  parens :: "prec"[prec_prod] :: except_mode[tex] :: math_prod{'x; 'A; 'B} =
   slot{'x} `":" slot{'A} " " times " " slot{'B}

dform pair_prl_df : except_mode[tex] :: except_mode[tex] :: math_pair{'a; 'b} =
   pushm[0] `"(" slot{'a}`"," slot{'b} `")" popm

dform spread_prl_df1 : parens :: "prec"[prec_spread] :: except_mode[tex] :: except_mode[tex] :: math_spread{'e; 'u; 'v; 'b} =
   szone pushm[1]
   keyword["match"] `" " slot{'e} `" " keyword["with"] hspace
      math_pair{'u; 'v} `" " Nuprl_font!rightarrow hspace
         slot{'b}
   popm ezone

dform fst_df1 : except_mode[tex] :: except_mode[tex] :: math_fst{'e} =
   slot{'e} `".1"

dform snd_df1 : except_mode[tex] :: except_mode[tex] :: math_snd{'e} =
   slot{'e} `".2"

declare and_df{'a}

dform and_df1 : except_mode[tex] :: parens :: "prec"[prec_and] :: math_and{'a; 'b} =
   szone pushm[0] slot["le"]{'a} and_df{'b} popm ezone

dform and_df2 : and_df{math_and{'a; 'b}} =
   and_df{'a} and_df{'b}

dform and_df3 : and_df{'a} =
   hspace Nuprl_font!wedge " " slot{'a}

declare cand_df{'a}

dform cand_df1 : except_mode[tex] :: parens :: "prec"[prec_and] :: math_cand{'a; 'b} =
   szone pushm[0] slot["le"]{'a} cand_df{'b} popm ezone

dform cand_df2 : and_df{math_cand{'a; 'b}} =
   cand_df{'a} cand_df{'b}

dform cand_df3 : cand_df{'a} =
   hspace Nuprl_font!wedge `"c" " " slot{'a}

dform exists_df1 : except_mode[tex] :: parens :: "prec"[prec_quant] :: except_mode[tex] :: math_exists{'x; 'A; 'B} =
   pushm[3] Nuprl_font!"exists" slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm

(************************************************************************
 * SET TYPE
 ************************************************************************)

declare math_set{'x; 'A; 'B}
declare math_squash{'A}

(************************************************
 * TeX mode
 *)

dform math_set_df1 : mode[tex] :: math_set{'x; 'A; 'B} =
   izone `"\\left\\{" ezone
   slot{'x}
   izone `"\\colon " ezone
   slot{'A} `"|" slot{'B}
   izone `"\\right\\}" ezone

dform math_squash_df1 : mode[tex] :: math_squash{'A} =
   izone `"\\sq{" ezone
   slot{'A}
   izone `"}" ezone

(************************************************
 * Normal mode
 *)
dform set_df1 : except_mode[tex] :: math_set{'x; 'A; 'B} =
   pushm[3] `"{" bvar{'x} `":" slot{'A} mid slot{'B} `"}" popm

dform math_squash_df2 : except_mode[tex] :: math_squash{'A} = "[" 'A "]"

(************************************************************************
 * Decidable
 ************************************************************************)

declare math_decidable{'P}

(************************************************
 * TeX mode
 *)

dform math_decidable_df1 : mode[tex] :: math_decidable{'P} =
   izone `"{{\\it decidable}(" ezone
   slot{'P}
   izone `")}" ezone

(************************************************
 * Normal mode
 *)
dform decidable_df1 : except_mode[tex] :: math_decidable{'A} =
   `"decidable(" slot{'A} `")"

(************************************************************************
 * INTERSECTION
 ************************************************************************)

declare math_isect{'x; 'A; 'B}
declare math_top
declare math_record{'t}
declare math_bisect{'A; 'B}

(************************************************
 * TeX mode
 *)

dform math_isect_df1 : mode[tex] :: math_isect{'x; 'A; 'B} =
   izone `"{\\bigcap_{" ezone
   slot{'x}
   izone `"\\colon " ezone
   slot{'A}
   izone `"} " ezone
   slot{'B}
   izone `"}" ezone

dform math_record_df1 : mode[tex] :: math_record{'t} =
   izone `"{\\left\\{" ezone
   slot{'t}
   izone `"\\right\\}}" ezone

dform math_bisect_df1 : mode[tex] :: math_bisect{'A; 'B} =
   izone `"{" ezone
   slot{'A}
   izone `"\\cap " ezone
   slot{'B}
   izone `"}" ezone

(************************************************
 * Normal mode
 *)
dform isect_df1 : except_mode[tex] :: math_isect{'x; 'A; 'B} =
   cap slot{'x} `":" slot{'A} `"." slot{'B}

dform top_df : math_top =
   math_i["Top"]

dform record_df : except_mode[tex] :: math_record{'t} =
   pushm[0] szone `"{ " pushm[0] 't popm hspace `"}" ezone popm

prec prec_bisect

dform bisect_df : except_mode[tex] :: parens :: "prec"[prec_bisect] :: math_bisect{'A; 'B} =
   slot["le"]{'A} `" " cap space slot{'B}

(************************************************************************
 * UNION
 ************************************************************************)

declare math_tunion{'x; 'A; 'B}
declare math_bunion{'A; 'B}

(************************************************
 * TeX mode
 *)

dform math_tunion_df1 : mode[tex] :: math_tunion{'x; 'A; 'B} =
   izone `"{\\bigcup_{" ezone
   slot{'x}
   izone `"\\colon " ezone
   slot{'A}
   izone `"} " ezone
   slot{'B}
   izone `"}" ezone

dform math_bunion_df1 : mode[tex] :: math_bunion{'A; 'B} =
   izone `"{" ezone
   slot{'A}
   izone `"\\cup " ezone
   slot{'B}
   izone `"}" ezone

(************************************************
 * Normal mode
 *)
dform tunion_df1 : except_mode[tex] :: math_tunion{'x; 'A; 'B} =
   cup slot{'x} `":" slot{'A} `"." slot{'B}

prec prec_bunion

dform bunion_df : except_mode[tex] :: parens :: "prec"[prec_bunion] :: math_bunion{'A; 'B} =
   slot["le"]{'A} `" " cup space slot{'B}

(************************************************************************
 * RECURSIVE TYPES
 ************************************************************************)

declare math_srec{'T; 'B}
declare math_prec{'T; 'y; 'B; 'a}
declare math_srecind{'t; 'a; 'b; 'c}
declare math_precind{'t; 'a; 'b; 'c}

declare math_w{'x; 'A; 'B}
declare math_tree{'a; 'f}
declare math_treeind{'z; 'a; 'f; 'g; 'body}

declare math_nil
declare math_cons{'a; 'b}
declare math_list{'l}
declare math_listind{'e; 'base; 'h; 't; 'f; 'step}

(************************************************
 * TeX mode
 *)
dform math_srec_df1 : mode[tex] :: math_srec{'T; 'B} =
   izone `"{\\mu(" ezone
   slot{'T}
   izone `"." ezone
   slot{'B}
   izone `")}" ezone

dform math_srecind_df1 : mode[tex] :: math_srecind{'t; 'a; 'b; 'c} =
   izone `"{{\\it srec\\_ind}(" ezone
   slot{'t}
   izone `";" ezone
   slot{'a}
   izone `"," ezone
   slot{'b}
   izone `"." ezone
   slot{'c}
   izone `")}" ezone

dform math_prec_df1 : mode[tex] :: math_prec{'T; 'x; 'B; 'a} =
   izone `"{\\mu(" ezone
   slot{'T}
   izone `"," ezone
   slot{'x}
   izone `"." ezone
   slot{'B}
   izone `";" ezone
   slot{'a}
   izone `")}" ezone

dform math_precind_df1 : mode[tex] :: math_precind{'t; 'a; 'b; 'c} =
   izone `"{{\\it prec\\_ind}(" ezone
   slot{'t}
   izone `";" ezone
   slot{'a}
   izone `"," ezone
   slot{'b}
   izone `"." ezone
   slot{'c}
   izone `")}" ezone

dform math_w_df1 : mode[tex] :: math_w{'x; 'A; 'B} =
   izone `"{\\mathop{\\it W}(" ezone
   slot{'x}
   izone `"\\colon " ezone
   slot{'A}
   izone `"." ezone
   slot{'B}
   izone `")}" ezone

dform math_tree_df1 : mode[tex] :: math_tree{'A; 'B} =
   izone `"{{\\it tree}(" ezone
   slot{'A}
   izone `";" ezone
   slot{'B}
   izone `")}" ezone

dform math_treeind_df1 : mode[tex] :: math_treeind{'t; 'a; 'b; 'c; 'd} =
   izone `"{{\\it prec\\_ind}(" ezone
   slot{'t}
   izone `";" ezone
   slot{'a}
   izone `"," ezone
   slot{'b}
   izone `"," ezone
   slot{'c}
   izone `"." ezone
   slot{'d}
   izone `")}" ezone

dform math_nil_df1 : mode[tex] :: math_nil =
   izone `"{\\it nil}" ezone

dform math_cons_df1 : mode[tex] :: math_cons{'h; 't} =
   izone `"{{\\it cons}(" ezone
   slot{'h}
   izone `"," ezone
   slot{'t}
   izone `")}" ezone

dform math_list_df1 : mode[tex] :: math_list{'l} =
   izone `"{{\\it list}(" ezone
   slot{'l}
   izone `")}" ezone

dform math_listind_df1 : mode[tex] :: math_listind{'e; 'base; 'h; 't; 'f; 'step} =
   izone `"{\\mathop{\\bf match}" ezone
   slot{'e}
   izone `"\\mathrel{\\bf with}" ezone
   math_cons{'h; 't}
   izone `"." ezone
   slot{'f}
   izone `"\\rightarrow " ezone
   slot{'step}
   izone `"}" ezone

(************************************************
 * Normal mode
 *)
dform srec_df : except_mode[tex] :: math_srec{'T; 'B} =
   szone mu `"{" slot{'T} `"." pushm[0] slot{'B} `"}" popm ezone

prec prec_w
prec prec_tree_ind

dform w_df : except_mode[tex] :: parens :: "prec"[prec_w] :: math_w{'x; 'A; 'B} =
   mathbbW slot{'x} `":" slot{'A} `"." slot{'B}

dform tree_df : except_mode[tex] :: math_tree{'a; 'f} =
   `"tree(" slot{'a} `"," " " slot{'f} `")"

dform tree_ind_df : except_mode[tex] :: parens :: "prec"[prec_tree_ind] :: math_treeind{'z; 'a; 'f; 'g; 'body} =
   szone pushm[3] `"tree_ind(" slot{'g} `"." " "
   pushm[3] `"let tree(" slot{'a} `", " slot{'f} `") =" space slot{'z} space `"in" popm space
   slot{'body} popm ezone

prec prec_cons
prec prec_list

declare search{'a; 'b}
declare semicolons{'a}
declare colons{'a}

(* Empty list *)
dform nil_df : except_mode[tex] :: math_nil = `"[]"

(* Search for nil entry *)
dform cons_df : except_mode[tex] :: math_cons{'a; 'b} =
   search{math_cons{'a; math_nil}; 'b}

(* Keep searching down the list *)
dform search_df1 : search{'a; math_cons{'b; 'c}} =
   search{math_cons{'b; 'a}; 'c}

(* Found a nil terminator: use bracket notation *)
dform search_df2 : search{'a; math_nil} =
   `"[" semicolons{'a} `"]"

(* No nil terminator, so use :: notation *)
dform search_df3 : search{'a; 'b} =
   colons{'a} `"::" slot{'b}

(* Reverse entries and separate with ; *)
dform semicolons_df1 : semicolons{math_cons{'a; math_nil}} =
   slot{'a}

dform semicolons_df2 : semicolons{math_cons{'a; 'b}} =
   semicolons{'b} `";" slot{'a}

(* Reverse entries and separate with :: *)
dform colons_df1 : colons{math_cons{'a; math_nil}} =
   slot{'a}

dform colons_df2 : colons{math_cons{'a; 'b}} =
   colons{'b} `"::" slot{'a}

dform list_df1 : except_mode[tex] :: parens :: "prec"[prec_list] :: math_list{'a} =
   slot{'a} `" List"

dform list_ind_df1 : except_mode[tex] :: parens :: "prec"[prec_list] :: math_listind{'e; 'base; 'h; 't; 'f; 'step} =
   szone pushm[1] pushm[3]
   `"match " slot{'e} `" with" hspace
   `"  [] ->" hspace slot{'base} popm hspace
   `"| " pushm[0] slot{'h} `"::" slot{'t} `"." slot{'f} `" ->" hspace slot{'step} popm popm ezone

(************************************************************************
 * QUOTIENT TYPE
 ************************************************************************)

declare math_quot{'T; 'x; 'y; 'E}
declare math_esquash{'P}

(************************************************
 * TeX
 *)
dform math_quot_df1 : mode[tex] :: math_quot{'T; 'x; 'y; 'E} =
   izone `"{" ezone
   slot{'x}
   izone `"," ezone
   slot{'y}
   izone `"\\colon " ezone
   slot{'T}
   izone `"// " ezone
   slot{'E}
   izone `"}" ezone

dform math_esquash_df1 : mode[tex] :: math_esquash{'P} =
   izone `"[\!" ezone
   `"[" slot{'P} `"]"
   izone `"\!]" ezone

(************************************************
 * Normal mode
 *)

prec prec_quot

dform quot_df1 : except_mode[tex] :: parens :: "prec"[prec_quot] :: math_quot{'A; 'x; 'y; 'E} =
   slot{'x} `", " slot{'y} `":" " " slot{'A} `" // " slot{'E}

dform math_esquash_df2 : except_mode[tex] :: math_esquash{'P} =
   `"[[" slot{'P} `"]]"

(************************************************************************
 * SUBSET
 ************************************************************************)

declare math_subset{'t1; 't2}

(************************************************
 * TeX mode
 *)

dform subset_df1 : mode[tex] :: math_subset{'t1; 't2} =
   izone `"{" ezone
   slot{'t1}
   izone `"\\subseteq_s " ezone
   slot{'t2}
   izone `"}" ezone

(************************************************
 * Normal mode
 *)

dform subset_df : except_mode[tex] :: math_subset{'t1; 't2} =
   slot{'t1} `" " subseteq `"s " slot{'t2}

(************************************************************************
 * GROUP THEORY
 ************************************************************************)

declare math_groupoid{'i}
declare math_semigroup{'i}
declare math_monoid{'i}
declare math_group{'i}
declare math_premonoid{'i}
declare math_pregroup{'i}

declare math_car{'g}
declare math_mul{'g; 'a; 'b}
declare math_id{'g}
declare math_inv{'g; 'a}

declare math_csemigroup{'i}
declare math_cmonoid{'i}
declare math_abelg{'i}

declare math_subStructure{'s; 'g}
declare math_subgroup{'i; 's; 'g}

declare math_lcoset{'h; 'g; 'a}
declare math_rcoset{'h; 'g; 'a}
declare math_normalSubg{'i; 's; 'g}

declare math_group_power{'g; 'a; 'n}
declare math_cycGroup{'g}
declare math_cycSubg{'g; 'a}

declare math_isInjective{'f; 'A; 'B}
declare math_isSurjective{'f; 'A; 'B}
declare math_isBijective{'f; 'A; 'B}
declare math_groupHom{'A; 'B}
declare math_groupMono{'A; 'B}
declare math_groupEpi{'A; 'B}
declare math_groupIso{'A; 'B}
declare math_groupKer{'f; 'A; 'B}

(************************************************
 * TeX mode
 *)

dform math_groupoid_df : mode[tex] :: math_groupoid{'i} =
   izone `"{{\\mathbb G} {roupoid}}_{" ezone
   slot{'i}
   izone `"}" ezone

dform math_semigroup_df : mode[tex] :: math_semigroup{'i} =
   izone `"{{\\mathbb S} {emigroup}}_{" ezone
   slot{'i}
   izone `"}" ezone

dform math_monoid_df : mode[tex] :: math_monoid{'i} =
   izone `"{{\\mathbb M} {onoid}}_{" ezone
   slot{'i}
   izone `"}" ezone

dform math_group_df : mode[tex] :: math_group{'i} =
   izone `"{{\\mathbb G} {roup}}_{" ezone
   slot{'i}
   izone `"}" ezone

dform math_premonoid_df : mode[tex] :: math_premonoid{'i} =
   izone `"{premonoid}_{" ezone
   slot{'i}
   izone `"}" ezone

dform math_pregroup_df : mode[tex] :: math_pregroup{'i} =
   izone `"{pregroup}_{" ezone
   slot{'i}
   izone `"}" ezone

dform math_car_df1 : mode[tex] :: math_car{'g} =
   izone `"car_{" ezone
   slot{'g}
   izone `"}" ezone

dform math_mul_df2 : mode[tex] :: math_mul{'g; 'i; 'j} =
   izone `"{" ezone
   slot{'i}
   izone `"*_{" ezone
   slot{'g}
   izone `"}" ezone
   slot{'j}
   izone `"}" ezone

dform math_id_df1 : mode[tex] :: math_id{'g} =
   izone `"1_{" ezone
   slot{'g}
   izone `"}" ezone

dform math_inv_df1 : mode[tex] :: math_inv{'g; 'i} =
   izone `"{" ezone
   slot{'i}
   izone `"}^{-1}_{" ezone
   slot{'g}
   izone `"}" ezone

dform math_csemigroup_df : mode[tex] :: math_csemigroup{'i} =
   izone `"{Commutative\\_semigroup}_{" ezone
   slot{'i}
   izone `"}" ezone

dform math_cmonoid_df : mode[tex] :: math_cmonoid{'i} =
   izone `"{Commutative\\_monoid}_{" ezone
   slot{'i}
   izone `"}" ezone

dform math_abelg_df : mode[tex] :: math_abelg{'i} =
   izone `"{Abelian\\_group}_{" ezone
   slot{'i}
   izone `"}" ezone

dform subStructure_df1 : mode[tex] :: math_subStructure{'s; 'g} =
   izone `"{" ezone
   slot{'s}
   izone `"\\subseteq_{str} " ezone
   slot{'g}
   izone `"}" ezone

dform subgroup_df1 : mode[tex] :: math_subgroup{'i; 's; 'g} =
   izone `"{\\it Subgroup}_{" ezone
   slot{'i}
   izone `"}(" ezone
   slot{'s}
   izone `"," ezone
   slot{'g}
   izone `")" ezone

dform lcoset_df1 : mode[tex] :: math_lcoset{'h; 'g; 'a} =
   izone `"{\\it Left\\_coset}(" ezone
   slot{'h}
   izone `"," ezone
   slot{'g}
   izone `"," ezone
   slot{'a}
   izone `")" ezone

dform rcoset_df1 : mode[tex] :: math_rcoset{'h; 'g; 'a} =
   izone `"{\\it Right\\_coset}(" ezone
   slot{'h}
   izone `"," ezone
   slot{'g}
   izone `"," ezone
   slot{'a}
   izone `")" ezone

dform normalSubg_df1 : mode[tex] :: math_normalSubg{'i; 's; 'g} =
   izone `"{\\it Normal\\_subgroup}_{" ezone
   slot{'i}
   izone `"}(" ezone
   slot{'s}
   izone `"," ezone
   slot{'g}
   izone `")" ezone

dform group_power_df1 : mode[tex] :: math_group_power{'g; 'a; 'n} =
   izone `"{" ezone
   slot{'a}
   izone `"}^{" ezone
   slot{'n}
   izone `"}_{" ezone
   slot{'g}
   izone `"}" ezone

dform cycGroup_df1 : mode[tex] :: math_cycGroup{'g} =
   izone `"{\\it Cyclic\\_group}(" ezone
   slot{'g}
   izone `")" ezone

dform cycSubg_df1 : mode[tex] :: math_cycSubg{'g; 'a} =
   izone `"{\\it Cyclic\\_subgroup}(" ezone
   slot{'g}
   izone `"," ezone
   slot{'a}
   izone `")" ezone

dform groupHom_df1 : mode[tex] :: math_groupHom{'A; 'B} =
   izone `"{\\it Group\\_homomorphism}(" ezone
   slot{'A}
   izone `"," ezone
   slot{'B}
   izone `")" ezone

dform math_isInjective_df1 : mode[tex] :: math_isInjective{'f; 'A; 'B} =
   'f
   izone `"\\colon " ezone
   'A
   izone `"\\rightarrow " ezone
   'B
   izone `"{\\it \\ is \\  injective}" ezone

dform math_isSurjective_df1 : mode[tex] :: math_isSurjective{'f; 'A; 'B} =
   'f
   izone `"\\colon " ezone
   'A
   izone `"\\rightarrow " ezone
   'B
   izone `"{\\it \\ is \\  surjective}" ezone

dform math_isBijective_df1 : mode[tex] :: math_isBijective{'f; 'A; 'B} =
   'f
   izone `"\\colon " ezone
   'A
   izone `"\\rightarrow " ezone
   'B
   izone `"{\\it \\ is \\  bijective}" ezone

dform groupMono_df1 : mode[tex] :: math_groupMono{'A; 'B} =
   izone `"{\\it Group\\_monomorphism}(" ezone
   slot{'A}
   izone `"," ezone
   slot{'B}
   izone `")" ezone

dform groupEpi_df1 : mode[tex] :: math_groupEpi{'A; 'B} =
   izone `"{\\it Group\\_epimorphism}(" ezone
   slot{'A}
   izone `"," ezone
   slot{'B}
   izone `")" ezone

dform groupIso_df1 : mode[tex] :: math_groupIso{'A; 'B} =
   izone `"{\\it Group\\_isomorphism}(" ezone
   slot{'A}
   izone `"," ezone
   slot{'B}
   izone `")" ezone

dform groupKer_df1 : mode[tex] :: math_groupKer{'f; 'A; 'B} =
   izone `"{\\it Group\\_kernel\\_of}(" ezone
   'f
   izone `"\\colon " ezone
   'A
   izone `"\\rightarrow " ezone
   'B
   izone `")" ezone

(************************************************
 * Normal mode
 *)

prec prec_inv
prec prec_mul < prec_inv

dform groupoid_df1 : except_mode[tex] :: math_groupoid{'i} =
   `"Groupoid[" slot{'i} `"]"

dform semigroup_df1 : except_mode[tex] :: math_semigroup{'i} =
   `"Semigroup[" slot{'i} `"]"

dform monoid_df1 : except_mode[tex] :: math_monoid{'i} =
   `"Monoid[" slot{'i} `"]"

dform group_df1 : except_mode[tex] :: math_group{'i} =
   `"Group[" slot{'i} `"]"

dform premonoid_df1 : except_mode[tex] :: math_premonoid{'i} =
   `"premonoid[" slot{'i} `"]"

dform pregroup_df1 : except_mode[tex] :: math_pregroup{'i} =
   `"pregroup[" slot{'i} `"]"

dform car_df1 : except_mode[tex] :: math_car{'g} =
   slot{'g} `".car"
(*   `"car_" slot{'g}*)

dform mul_df2 : except_mode[tex] :: parens :: "prec"[prec_mul] :: math_mul{'g; 'a; 'b} =
   slot["lt"]{'a} `" *_" slot{'g} `" " slot["le"]{'b}

dform id_df1 : except_mode[tex] :: math_id{'g} =
   slot{'g} `".1"
(*   `"1_" slot{'g}*)

dform inv_df1 : except_mode[tex] :: parens :: "prec"[prec_inv] :: math_inv{'g; 'a} =
   slot{'g} `".inv " slot{'a}
(*   `"inv_" slot{'g} `" " slot{'a}*)

dform csemigroup_df1 : except_mode[tex] :: math_csemigroup{'i} =
   `"Commutative_semiroup[" slot{'i} `"]"

dform cmonoid_df1 : except_mode[tex] :: math_cmonoid{'i} =
   `"Commutative_monoid[" slot{'i} `"]"

dform abelg_df1 : except_mode[tex] :: math_abelg{'i} =
   `"Abelian_group[" slot{'i} `"]"

dform subStructure_df : except_mode[tex] :: math_subStructure{'s; 'g} =
   slot{'s} `" " subseteq `"str " slot{'g}

dform subgroup_df : except_mode[tex] :: math_subgroup{'i; 's; 'g} =
   `"Subgroup[" slot{'i} `"](" slot{'s} `"; " slot{'g} `")"

dform lcoset_df : parens :: except_mode[tex] :: math_lcoset{'h; 'g; 'a} =
   `"Left_coset(" slot{'h} `"; " slot{'g} `"; " slot{'a} `")"

dform rcoset_df : parens :: except_mode[tex] :: math_rcoset{'h; 'g; 'a} =
   `"Right_coset(" slot{'h} `"; " slot{'g} `"; " slot{'a} `")"

dform normalSubg_df : except_mode[tex] :: math_normalSubg{'i; 's; 'g} =
   `"Normal_subgroup[" slot{'i} `"](" slot{'s} `"; " slot{'g} `")"

dform group_power_df1 : except_mode[tex] :: parens :: "prec"[prec_inv] :: math_group_power{'g; 'a; 'n} =
   slot{'g} `".power(" slot{'a} `"; " slot{'n} `")"

dform cycGroup_df : except_mode[src] :: math_cycGroup{'g} =
   `"Cyclic_group(" slot{'g} `")"

dform cycSubg_df : except_mode[tex] :: math_cycSubg{'g; 'a} =
   `"Cyclic_subgroup(" slot{'g} `"; " slot{'a} `")"

dform groupHom_df : except_mode[tex] :: math_groupHom{'A; 'B} =
   `"Group_homomorphism(" slot{'A} `"; " slot{'B}  `")"

dform isInjective_df : except_mode[tex] :: math_isInjective{'f; 'A; 'B} =
   `"(" slot{'f} `":" slot{'A} " " rightarrow " " slot{'B}  `") is injective"

dform isSurjective_df : except_mode[tex] :: math_isSurjective{'f; 'A; 'B} =
   `"(" slot{'f} `":" slot{'A} " " rightarrow " " slot{'B}  `") is surjective"

dform isBijective_df : except_mode[tex] :: math_isBijective{'f; 'A; 'B} =
   `"(" slot{'f} `":" slot{'A} " " rightarrow " " slot{'B}  `") is bijective"

dform groupMono_df : except_mode[tex] :: math_groupMono{'A; 'B} =
   `"Group_monomorphism(" slot{'A} `"; " slot{'B}  `")"

dform groupEpi_df : except_mode[tex] :: math_groupEpi{'A; 'B} =
   `"Group_epimorphism(" slot{'A} `"; " slot{'B}  `")"

dform groupIso_df : except_mode[tex] :: math_groupIso{'A; 'B} =
   `"Group_isomorphism(" slot{'A} `"; " slot{'B}  `")"

dform groupKer_df : except_mode[tex] :: math_groupKer{'f; 'A; 'B} =
   `"Group_kernel_of (" slot{'f} `":" slot{'A} " " rightarrow " " slot{'B} `")"

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
