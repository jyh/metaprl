(*
 * characters in the Nuprl font.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * jyh@cs.cornell.edu
 *)

open Printf
open Mp_debug

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Nuprl_font%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Display control.
 *)
declare pagebreak

(*
 * Fonts.
 * Each of these can be used with a string, with a term,
 * or unbalanced.
 *
 * For example, all of these are the same:
 *    bf["["]
 *    bf{"["}
 *    bf_begin "[" bf_end
 *)
declare info[name:s]
declare info_begin
declare info_end
declare keyword[name:s]
declare keyword_begin
declare keyword_end
declare bf[name:s]
declare bf_begin
declare bf_end
declare it[name:s]
declare it_begin
declare it_end
declare sym[name:s]
declare sym_begin
declare sym_end
declare em[name:s]
declare em_begin
declare em_end
declare tt[name:s]
declare tt_begin
declare tt_end
declare sub[name:s]
declare sub_begin
declare sub_end
declare sup[name:s]
declare sup_begin
declare sup_end
declare small[name:s]
declare small_begin
declare small_end

(*
 * HTML control.
 *)
declare cd_begin[command:s]
declare cd_end

(* Displays *)
declare mathbbA
declare mathbbB
declare mathbbC
declare mathbbD
declare mathbbE
declare mathbbF
declare mathbbG
declare mathbbH
declare mathbbI
declare mathbbJ
declare mathbbK
declare mathbbL
declare mathbbM
declare mathbbN
declare mathbbO
declare mathbbP
declare mathbbQ
declare mathbbR
declare mathbbS
declare mathbbT
declare mathbbU
declare mathbbV
declare mathbbW
declare mathbbX
declare mathbbY
declare mathbbZ

declare shortLeftarrow
declare Leftarrow
declare Middlearrow
declare shortRightarrow
declare Rightarrow
declare Leftrightarrow
declare ulcorner
declare urcorner
declare vdash
declare integral
declare cdot
declare downarrow
declare uparrow
declare alpha
declare beta
declare pi
declare lambda
declare gamma
declare delta
declare rho
declare sigma
declare epsilon
declare eta
declare theta
declare iota
declare kappa
declare mu
declare nu
declare omicron
declare tau
declare phi
declare xi
declare omega

declare wedge
declare tneg
declare member
declare plusminus
declare oplus
declare infty
declare partial
declare subset
declare supset
declare cap
declare cup
declare forall
declare "exists"
declare oinfty
declare shortleftrightarrow
declare shortleftarrow
declare shortrightarrow
declare longleftrightarrow
declare longleftarrow
declare longrightarrow
declare neq
declare sim
declare le
declare ge
declare equiv
declare vee
declare leftarrow
declare middlearrow
declare rightarrow
declare Sigma
declare Delta
declare Pi
declare times
declare "div"
declare supplus
declare supminus
declare supcirc
declare subseteq
declare supseteq
declare subzero
declare subone
declare subtwo
declare subthree
declare suba
declare subb
declare subc
declare subq
declare subz

(************************************************************************
 * DISPLAY CONTROL                                                      *
 ************************************************************************)

(*
 * Pagebreak works only in prl mode.
 *)
dform pagebreak_df1 : pagebreak = `""

dform pagebreak_df2 : mode["prl"] :: pagebreak =
   `"\012"

(************************************************************************
 * HTML                                                                 *
 ************************************************************************)

(*
 * Change directory.
 *)
dform cd_begin_df1 : internal :: cd_begin[name:s] =
   `""

dform cd_begin_df2 : internal :: mode[html] :: cd_begin[name:s] =
   izone `"<a href=\"http://cd.metaprl.local//" slot[name:s] `"\">" ezone

dform cd_end_df1 : internal :: cd_end =
   `""

dform cd_end_df2 : internal :: mode[html] :: cd_end =
   izone `"</a>" ezone

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform info_begin_df : internal :: info_begin =
   izone `"<font color=\"#115599\"><b>" ezone

dform info_end_df : internal :: info_end =
   izone `"</b></font>" ezone

dform info_df1 : internal :: info[text:s] =
   info_begin slot[text:s] info_end

dform info_df2 : internal :: info{'t} =
   info_begin 't info_end

dform keyword_begin_df : internal :: keyword_begin =
   izone `"<font color=\"#551155\"><b>" ezone

dform keyword_end_df : internal :: keyword_end =
   izone `"</b></font>" ezone

dform keyword_df1 : internal :: keyword[text:s] =
   keyword_begin slot[text:s] keyword_end

dform keyword_df2 : internal :: keyword{'t} =
   keyword_begin 't keyword_end

dform bf_begin_df : internal :: bf_begin =
   izone `"<b>" ezone

dform bf_end_df : internal :: bf_end =
   izone `"</b>" ezone

dform bf_df1 : internal :: bf[text:s] =
   bf_begin slot[text:s] bf_end

dform bf_df2 : internal :: bf{'t} =
   bf_begin 't bf_end

dform it_begin_df : internal :: it_begin =
   izone `"<b>" ezone

dform it_end_df : internal :: it_end =
   izone `"</b>" ezone

dform it_df1 : internal :: it[text:s] =
   it_begin slot[text:s] it_end

dform it_df2 : internal :: it{'t} =
   it_begin 't it_end

dform sym_begin_df : internal :: sym_begin =
   izone `"<b>" ezone

dform sym_end_df : internal :: sym_end =
   izone `"</b>" ezone

dform sym_df1 : internal :: sym[text:s] =
   sym_begin slot[text:s] sym_end

dform sym_df2 : internal :: sym{'t} =
   sym_begin 't sym_end

dform em_begin_df : internal :: em_begin =
   izone `"<em>" ezone

dform em_end_df : internal :: em_end =
   izone `"</em>" ezone

dform em_df1 : internal :: em[text:s] =
   em_begin slot[text:s] em_end

dform em_df2 : internal :: em{'t} =
   em_begin 't em_end

dform tt_begin_df : internal :: tt_begin =
   izone `"<tt>" ezone

dform tt_end_df : internal :: tt_end =
   izone `"</tt>" ezone

dform tt_df1 : internal :: tt[text:s] =
   tt_begin slot[text:s] tt_end

dform tt_df2 : internal :: tt{'t} =
   tt_begin 't tt_end

dform sub_begin_df : internal :: sub_begin =
   izone `"<sub>" ezone

dform sub_end_df : internal :: sub_end =
   izone `"</sub>" ezone

dform sub_df1 : internal :: sub[text:s] =
   sub_begin slot[text:s] sub_end

dform sub_df2 : internal :: sub{'t} =
   sub_begin 't sub_end

dform sup_begin_df : internal :: sup_begin =
   izone `"<sup>" ezone

dform sup_end_df : internal :: sup_end =
   izone `"</sup>" ezone

dform sup_df1 : internal :: sup[text:s] =
   sup_begin slot[text:s] sup_end

dform sup_df2 : internal :: sup{'t} =
   sup_begin 't sup_end

dform small_begin_df : internal :: small_begin =
   izone `"<small>" ezone

dform small_end_df : internal :: small_end =
   izone `"</small>" ezone

dform small_df1 : internal :: small[text:s] =
   small_begin slot[text:s] small_end

dform small_df2 : internal :: small{'t} =
   small_begin 't small_end

(************************************************************************
 * TEX HELPERS                                                          *
 ************************************************************************)

declare mathBB[name:s]
declare ensuremath[name:s]
declare mathmacro[name:s]

dform mathBB_df : internal :: mode[tex] :: mathBB[text:s] =
   izone `"$\\mathbb " ezone slot[text:s] izone `"$" ezone

dform ensuremath_df : internal :: mode[tex] :: ensuremath[text:s] =
   izone `"$" ezone slot[text:s] izone `"$" ezone

dform mathmacro_df : internal :: mode[tex] :: mathmacro[text:s] =
   izone `"$\\" slot[text:s] `"$" ezone

dform info_begin_df : internal :: mode[tex] :: info_begin =
   izone `"{\\bf " ezone

dform info_end_df : internal :: mode[tex] :: info_end =
   izone `"}" ezone

dform keyword_begin_df : internal :: mode[tex] :: keyword_begin =
   izone `"{\\bf " ezone

dform keyword_end_df : internal :: mode[tex] :: keyword_end =
   izone `"}" ezone

dform bf_begin_df : internal :: mode[tex] :: bf_begin =
   izone `"{\\bf " ezone

dform bf_end_df : internal :: mode[tex] :: bf_end =
   izone `"}" ezone

dform it_begin_df : internal :: mode[tex] :: it_begin =
   izone `"{\\it " ezone

dform it_end_df : internal :: mode[tex] :: it_end =
   izone `"\\/}" ezone

dform sym_begin_df : internal :: mode[tex] :: sym_begin =
   izone `"{\\bf " ezone

dform sym_end_df : internal :: mode[tex] :: sym_end =
   izone `"}" ezone

dform em_begin_df : internal :: mode[tex] :: em_begin =
   izone `"{\\em " ezone

dform em_end_df : internal :: mode[tex] :: em_end =
   izone `"\\/}" ezone

dform tt_begin_df : internal :: mode[tex] :: tt_begin =
   izone `"{\\tt " ezone

dform tt_end_df : internal :: mode[tex] :: tt_end =
   izone `"}" ezone

dform sub_begin_df : internal :: mode[tex] :: sub_begin =
   izone `"$_{" ezone

dform sub_end_df : internal :: mode[tex] :: sub_end =
   izone `"}$" ezone

dform sup_begin_df : internal :: mode[tex] :: sup_begin =
   izone `"$^{" ezone

dform sup_end_df : internal :: mode[tex] :: sup_end =
   izone `"}$" ezone

dform small_begin_df : internal :: mode[tex] :: small_begin =
   izone `"{\\scriptsize " ezone

dform small_end_df : internal :: mode[tex] :: small_end =
   izone `"}" ezone

(************************************************************************
 * NUPRL FONT                                                           *
 ************************************************************************)

(* Displays *)
dform mathbbA_df		: internal :: mode[prl] :: mathbbA                   = `"\129"
dform mathbbB_df		: internal :: mode[prl] :: mathbbB                   = `"\130"
dform mathbbC_df		: internal :: mode[prl] :: mathbbC                   = `"\131"
dform mathbbD_df		: internal :: mode[prl] :: mathbbD                   = `"\132"
dform mathbbE_df		: internal :: mode[prl] :: mathbbE                   = `"\133"
dform mathbbF_df		: internal :: mode[prl] :: mathbbF                   = `"\134"
dform mathbbG_df		: internal :: mode[prl] :: mathbbG                   = `"\135"
dform mathbbH_df		: internal :: mode[prl] :: mathbbH                   = `"\136"
dform mathbbI_df		: internal :: mode[prl] :: mathbbI                   = `"\137"
dform mathbbJ_df		: internal :: mode[prl] :: mathbbJ                   = `"\138"
dform mathbbK_df		: internal :: mode[prl] :: mathbbK                   = `"\139"
(* dform mathbbL_df		: internal :: mode[prl] :: mathbbL                   = `"\140" *)
dform mathbbM_df		: internal :: mode[prl] :: mathbbN                   = `"\141"
dform mathbbN_df		: internal :: mode[prl] :: mathbbO                   = `"\142"
dform mathbbO_df		: internal :: mode[prl] :: mathbbP                   = `"\143"
dform mathbbP_df		: internal :: mode[prl] :: mathbbQ                   = `"\144"
dform mathbbQ_df		: internal :: mode[prl] :: mathbbR                   = `"\145"
dform mathbbR_df		: internal :: mode[prl] :: mathbbS                   = `"\146"
dform mathbbS_df		: internal :: mode[prl] :: mathbbT                   = `"\147"
dform mathbbT_df		: internal :: mode[prl] :: mathbbU                   = `"\148"
dform mathbbU_df		: internal :: mode[prl] :: mathbbV                   = `"\149"
dform mathbbV_df		: internal :: mode[prl] :: mathbbW                   = `"\150"
dform mathbbW_df		: internal :: mode[prl] :: mathbbX                   = `"\151"
dform mathbbX_df		: internal :: mode[prl] :: mathbbY                   = `"\152"
dform mathbbY_df		: internal :: mode[prl] :: mathbbZ                   = `"\153"

dform mathbbA_df		: internal :: mode[html] :: mathbbA                   = keyword["A"]
dform mathbbB_df		: internal :: mode[html] :: mathbbB                   = keyword["B"]
dform mathbbC_df		: internal :: mode[html] :: mathbbC                   = keyword["C"]
dform mathbbD_df		: internal :: mode[html] :: mathbbD                   = keyword["D"]
dform mathbbE_df		: internal :: mode[html] :: mathbbE                   = keyword["E"]
dform mathbbF_df		: internal :: mode[html] :: mathbbF                   = keyword["F"]
dform mathbbG_df		: internal :: mode[html] :: mathbbG                   = keyword["G"]
dform mathbbH_df		: internal :: mode[html] :: mathbbH                   = keyword["H"]
dform mathbbI_df		: internal :: mode[html] :: mathbbI                   = keyword["I"]
dform mathbbJ_df		: internal :: mode[html] :: mathbbJ                   = keyword["J"]
dform mathbbK_df		: internal :: mode[html] :: mathbbK                   = keyword["K"]
dform mathbbL_df		: internal :: mode[html] :: mathbbL                   = keyword["L"]
dform mathbbM_df		: internal :: mode[html] :: mathbbM                   = keyword["M"]
dform mathbbN_df		: internal :: mode[html] :: mathbbN                   = sym["&#8469;"]
dform mathbbO_df		: internal :: mode[html] :: mathbbO                   = keyword["O"]
dform mathbbP_df		: internal :: mode[html] :: mathbbP                   = sym["&#8473;"]
dform mathbbQ_df		: internal :: mode[html] :: mathbbQ                   = sym["&#8474;"]
dform mathbbR_df		: internal :: mode[html] :: mathbbR                   = sym["&#8477;"]
dform mathbbS_df		: internal :: mode[html] :: mathbbS                   = keyword["S"]
dform mathbbT_df		: internal :: mode[html] :: mathbbT                   = keyword["T"]
dform mathbbU_df		: internal :: mode[html] :: mathbbU                   = keyword["U"]
dform mathbbV_df		: internal :: mode[html] :: mathbbV                   = keyword["V"]
dform mathbbW_df		: internal :: mode[html] :: mathbbW                   = keyword["W"]
dform mathbbX_df		: internal :: mode[html] :: mathbbX                   = keyword["X"]
dform mathbbY_df		: internal :: mode[html] :: mathbbY                   = keyword["Y"]
dform mathbbZ_df		: internal :: mode[html] :: mathbbZ                   = sym["&#8484;"]

dform mathbbA_df		: internal :: mode[tex] :: mathbbA                   = mathBB["A"]
dform mathbbB_df		: internal :: mode[tex] :: mathbbB                   = mathBB["B"]
dform mathbbC_df		: internal :: mode[tex] :: mathbbC                   = mathBB["C"]
dform mathbbD_df		: internal :: mode[tex] :: mathbbD                   = mathBB["D"]
dform mathbbE_df		: internal :: mode[tex] :: mathbbE                   = mathBB["E"]
dform mathbbF_df		: internal :: mode[tex] :: mathbbF                   = mathBB["F"]
dform mathbbG_df		: internal :: mode[tex] :: mathbbG                   = mathBB["G"]
dform mathbbH_df		: internal :: mode[tex] :: mathbbH                   = mathBB["H"]
dform mathbbI_df		: internal :: mode[tex] :: mathbbI                   = mathBB["I"]
dform mathbbJ_df		: internal :: mode[tex] :: mathbbJ                   = mathBB["J"]
dform mathbbK_df		: internal :: mode[tex] :: mathbbK                   = mathBB["K"]
dform mathbbL_df		: internal :: mode[tex] :: mathbbL                   = mathBB["L"]
dform mathbbM_df		: internal :: mode[tex] :: mathbbM                   = mathBB["M"]
dform mathbbN_df		: internal :: mode[tex] :: mathbbN                   = mathBB["N"]
dform mathbbO_df		: internal :: mode[tex] :: mathbbO                   = mathBB["O"]
dform mathbbP_df		: internal :: mode[tex] :: mathbbP                   = mathBB["P"]
dform mathbbQ_df		: internal :: mode[tex] :: mathbbQ                   = mathBB["Q"]
dform mathbbR_df		: internal :: mode[tex] :: mathbbR                   = mathBB["R"]
dform mathbbS_df		: internal :: mode[tex] :: mathbbS                   = mathBB["S"]
dform mathbbT_df		: internal :: mode[tex] :: mathbbT                   = mathBB["T"]
dform mathbbU_df		: internal :: mode[tex] :: mathbbU                   = mathBB["U"]
dform mathbbV_df		: internal :: mode[tex] :: mathbbV                   = mathBB["V"]
dform mathbbW_df		: internal :: mode[tex] :: mathbbW                   = mathBB["W"]
dform mathbbX_df		: internal :: mode[tex] :: mathbbX                   = mathBB["X"]
dform mathbbY_df		: internal :: mode[tex] :: mathbbY                   = mathBB["Y"]
dform mathbbZ_df		: internal :: mode[tex] :: mathbbZ                   = mathBB["Z"]

dform shortLeftarrow_df		: internal :: mode[prl] :: shortLeftarrow            = `"\1565"
dform leftarrow_df		: internal :: mode[prl] :: Leftarrow                 = `"\220\221"
dform middlearrow_df		: internal :: mode[prl] :: Middlearrow               = `"\221"
dform shortRightarrow_df	: internal :: mode[prl] :: shortRightarrow           = `"\158"
dform rightarrow_df		: internal :: mode[prl] :: Rightarrow                = `"\157\158"
dform leftrightarrow_df		: internal :: mode[prl] :: Leftrightarrow            = `"\220\221\222"
dform ulcorner_df		: internal :: mode[prl] :: ulcorner                  = `"\154"
dform urcorner_df		: internal :: mode[prl] :: urcorner                  = `"\155"
dform vdash_df                  : internal :: mode[prl] :: vdash                     = `"\159"
dform integral_df		: internal :: mode[prl] :: integral                  = `"\160"
dform cdot_df                   : internal :: mode[prl] :: cdot                      = `"\204"
dform downarrow_df		: internal :: mode[prl] :: downarrow                 = `"\205"
dform uparrow_df		: internal :: mode[prl] :: uparrow                   = `"\206"
dform alpha_df                  : internal :: mode[prl] :: alpha                     = `"\161"
dform beta_df			: internal :: mode[prl] :: beta                      = `"\162"
dform pi_df			: internal :: mode[prl] :: pi                        = `"\176"
dform lambda_df			: internal :: mode[prl] :: lambda                    = `"\171"
dform gamma_df			: internal :: mode[prl] :: gamma                     = `"\163"
dform delta_df			: internal :: mode[prl] :: delta                     = `"\164"
dform rho_df			: internal :: mode[prl] :: rho                       = `"\177"
dform sigma_df			: internal :: mode[prl] :: sigma                     = `"\178"
dform epsilon_df		: internal :: mode[prl] :: epsilon                   = `"\165"
dform eta_df			: internal :: mode[prl] :: eta                       = `"\167"
dform theta_df			: internal :: mode[prl] :: theta                     = `"\168"
dform iota_df			: internal :: mode[prl] :: iota                      = `"\169"
dform kappa_df			: internal :: mode[prl] :: kappa                     = `"\170"
dform mu_df			: internal :: mode[prl] :: mu                        = `"\172"
dform nu_df			: internal :: mode[prl] :: nu                        = `"\173"
dform omicron_df		: internal :: mode[prl] :: omicron                   = `"\175"
dform tau_df			: internal :: mode[prl] :: tau                       = `"\179"
dform phi_df			: internal :: mode[prl] :: phi                       = `"\181"
dform xi_df			: internal :: mode[prl] :: xi                        = `"\182"
dform omega_df			: internal :: mode[prl] :: omega                     = `"\184"

dform shortLeftarrow_df		: internal :: mode[html] :: shortLeftarrow            = sym["&#8656;"]
dform leftarrow_df		: internal :: mode[html] :: Leftarrow                 = sym["&#8656;"]
dform middlearrow_df		: internal :: mode[html] :: Middlearrow               = sym["&#8660;"]
dform shortRightarrow_df	: internal :: mode[html] :: shortRightarrow           = sym["&#8658;"]
dform rightarrow_df		: internal :: mode[html] :: Rightarrow                = sym["&#8658;"]
dform leftrightarrow_df		: internal :: mode[html] :: Leftrightarrow            = sym["&#8660;"]
dform ulcorner_df		: internal :: mode[html] :: ulcorner                  = sym["&#8968;"]
dform urcorner_df		: internal :: mode[html] :: urcorner                  = sym["&#8969;"]
dform vdash_df                  : internal :: mode[html] :: vdash                     = sym["&#8866;"]
dform integral_df		: internal :: mode[html] :: integral                  = sym["&#8747;"]
dform cdot_df                   : internal :: mode[html] :: cdot                      = keyword["&middot;"]
dform downarrow_df		: internal :: mode[html] :: downarrow                 = sym["&#8595;"]
dform uparrow_df		: internal :: mode[html] :: uparrow                   = sym["&#8593;"]
dform alpha_df                  : internal :: mode[html] :: alpha                     = sym["&#945;"]
dform beta_df			: internal :: mode[html] :: beta                      = sym["&#946;"]
dform pi_df			: internal :: mode[html] :: pi                        = sym["&#960;;"]
dform lambda_df			: internal :: mode[html] :: lambda                    = sym["&#955;"]
dform gamma_df			: internal :: mode[html] :: gamma                     = sym["&#947;"]
dform delta_df			: internal :: mode[html] :: delta                     = sym["&#948;"]
dform rho_df			: internal :: mode[html] :: rho                       = sym["&#961;"]
dform sigma_df			: internal :: mode[html] :: sigma                     = sym["&#963;"]
dform epsilon_df		: internal :: mode[html] :: epsilon                   = sym["&#949;"]
dform eta_df			: internal :: mode[html] :: eta                       = sym["&#951;"]
dform theta_df			: internal :: mode[html] :: theta                     = sym["&#952;"]
dform iota_df			: internal :: mode[html] :: iota                      = sym["&#953;"]
dform kappa_df			: internal :: mode[html] :: kappa                     = sym["&#954;"]
dform mu_df			: internal :: mode[html] :: mu                        = sym["&#956;"]
dform nu_df			: internal :: mode[html] :: nu                        = sym["&#957;"]
dform omicron_df		: internal :: mode[html] :: omicron                   = sym["&#959;"]
dform tau_df			: internal :: mode[html] :: tau                       = sym["&#964;"]
dform phi_df			: internal :: mode[html] :: phi                       = sym["&#966;"]
dform xi_df			: internal :: mode[html] :: xi                        = sym["&#967;"]
dform omega_df			: internal :: mode[html] :: omega                     = sym["&#969;"]

dform shortLeftarrow_df		: internal :: mode[tex] :: shortLeftarrow            = mathmacro["leftarrow"]
dform leftarrow_df		: internal :: mode[tex] :: Leftarrow                 = mathmacro["leftarrow"]
dform middlearrow_df		: internal :: mode[tex] :: Middlearrow               = mathmacro["-"]
dform shortRightarrow_df	: internal :: mode[tex] :: shortRightarrow           = mathmacro["rightarrow"]
dform rightarrow_df		: internal :: mode[tex] :: Rightarrow                = mathmacro["rightarrow"]
dform leftrightarrow_df		: internal :: mode[tex] :: Leftrightarrow            = mathmacro["leftrightarrow"]
dform ulcorner_df		: internal :: mode[tex] :: ulcorner                  = mathmacro["ulcorner"]
dform urcorner_df		: internal :: mode[tex] :: urcorner                  = mathmacro["urcorner"]
dform vdash_df                  : internal :: mode[tex] :: vdash                     = mathmacro["vdash"]
dform integral_df		: internal :: mode[tex] :: integral                  = mathmacro["int"]
dform cdot_df                   : internal :: mode[tex] :: cdot                      = mathmacro["cdot"]
dform downarrow_df		: internal :: mode[tex] :: downarrow                 = mathmacro["downarrow"]
dform uparrow_df		: internal :: mode[tex] :: uparrow                   = mathmacro["uparrow"]
dform alpha_df                  : internal :: mode[tex] :: alpha                     = mathmacro["alpha"]
dform beta_df			: internal :: mode[tex] :: beta                      = mathmacro["beta"]
dform pi_df			: internal :: mode[tex] :: pi                        = mathmacro["pi"]
dform lambda_df			: internal :: mode[tex] :: lambda                    = mathmacro["lambda"]
dform gamma_df			: internal :: mode[tex] :: gamma                     = mathmacro["gamma"]
dform delta_df			: internal :: mode[tex] :: delta                     = mathmacro["delta"]
dform rho_df			: internal :: mode[tex] :: rho                       = mathmacro["rho"]
dform sigma_df			: internal :: mode[tex] :: sigma                     = mathmacro["sigma"]
dform epsilon_df		: internal :: mode[tex] :: epsilon                   = mathmacro["epsilon"]
dform eta_df			: internal :: mode[tex] :: eta                       = mathmacro["eta"]
dform theta_df			: internal :: mode[tex] :: theta                     = mathmacro["theta"]
dform iota_df			: internal :: mode[tex] :: iota                      = mathmacro["iota"]
dform kappa_df			: internal :: mode[tex] :: kappa                     = mathmacro["kappa"]
dform mu_df			: internal :: mode[tex] :: mu                        = mathmacro["mu"]
dform nu_df			: internal :: mode[tex] :: nu                        = mathmacro["nu"]
dform omicron_df		: internal :: mode[tex] :: omicron                   = mathmacro["omicron"]
dform tau_df			: internal :: mode[tex] :: tau                       = mathmacro["tau"]
dform phi_df			: internal :: mode[tex] :: phi                       = mathmacro["phi"]
dform xi_df			: internal :: mode[tex] :: xi                        = mathmacro["xi"]
dform omega_df			: internal :: mode[tex] :: omega                     = mathmacro["omega"]

dform wedge_df			: internal :: mode[prl] :: wedge                     = `"\207"
dform tneg_df			: internal :: mode[prl] :: tneg                      = `"\191"
dform member_df			: internal :: mode[prl] :: member                    = `"\209"
dform plusminus_df		: internal :: mode[prl] :: plusminus                 = `"\210"
dform oplus_df			: internal :: mode[prl] :: oplus                     = `"XXX"
dform infty_df			: internal :: mode[prl] :: infty                     = `"XXX"
dform partial_df		: internal :: mode[prl] :: partial                   = `"\211"
dform subset_df			: internal :: mode[prl] :: subset                    = `"\212"
dform supset_df			: internal :: mode[prl] :: supset                    = `"\213"
dform cap_df			: internal :: mode[prl] :: cap                       = `"\214"
dform cup_df			: internal :: mode[prl] :: cup                       = `"\215"
dform forall_df			: internal :: mode[prl] :: forall                    = `"\216"
dform exists_df			: internal :: mode[prl] :: "exists"                  = `"\217"
dform oinfty_df			: internal :: mode[prl] :: oinfty                    = `"XXX"
dform shortleftrightarrow_df	: internal :: mode[prl] :: shortleftrightarrow       = `"\165"
dform shortleftarrow_df		: internal :: mode[prl] :: shortleftarrow            = `"\220"
dform shortrightarrow_df	: internal :: mode[prl] :: shortrightarrow           = `"\222"
dform longleftrightarrow_df	: internal :: mode[prl] :: longleftrightarrow        = `"\223\221\221\222"
dform longleftarrow_df		: internal :: mode[prl] :: longleftarrow             = `"\220\221\221"
dform longrightarrow_df		: internal :: mode[prl] :: longrightarrow            = `"\221\221\222"
dform neq_df			: internal :: mode[prl] :: neq                       = `"225"
dform sim_df			: internal :: mode[prl] :: sim                       = `"XXX"
dform le_df			: internal :: mode[prl] :: le                        = `"\218"
dform ge_df			: internal :: mode[prl] :: ge                        = `"\219"
dform equiv_df			: internal :: mode[prl] :: equiv                     = `"\226"
dform vee_df			: internal :: mode[prl] :: vee                       = `"\208"
dform leftarrow_df		: internal :: mode[prl] :: leftarrow                 = `"\223\221"
dform middlearrow_df		: internal :: mode[prl] :: middlearrow               = `"\221"
dform rightarrow_df		: internal :: mode[prl] :: rightarrow                = `"\221\222"
dform sigma_df			: internal :: mode[prl] :: Sigma                     = `"\199"
dform delta_df			: internal :: mode[prl] :: Delta                     = `"\194"
dform pi_df			: internal :: mode[prl] :: Pi                        = `"\198"
dform times_df			: internal :: mode[prl] :: times                     = `"\227"
dform div_df            	: internal :: mode[prl] :: "div"                     = `"\228"
dform supplus_df		: internal :: mode[prl] :: supplus                   = `"\229"
dform supminus_df		: internal :: mode[prl] :: supminus                  = `"\230"
dform supcirc_df		: internal :: mode[prl] :: supcirc                   = `"\231"
dform subseteq_df		: internal :: mode[prl] :: subseteq                  = `"\232"
dform supseteq_df		: internal :: mode[prl] :: supseteq                  = `"\233"
dform subzero_df		: internal :: mode[prl] :: subzero                   = `"\240"
dform subone_df			: internal :: mode[prl] :: subone                    = `"\241"
dform subtwo_df			: internal :: mode[prl] :: subtwo                    = `"\242"
dform subthree_df		: internal :: mode[prl] :: subthree                  = `"\244"
dform suba_df			: internal :: mode[prl] :: suba                      = `"\237"
dform subb_df			: internal :: mode[prl] :: subb                      = `"\236"
dform subc_df			: internal :: mode[prl] :: subc                      = `"\238"
dform subq_df			: internal :: mode[prl] :: subq                      = `"XXX"
dform subz_df			: internal :: mode[prl] :: subz                      = `"\235"

dform wedge_df			: internal :: mode[html] :: wedge                     = sym["&#8744;"]
dform tneg_df			: internal :: mode[html] :: tneg                      = keyword["&not;"]
dform member_df			: internal :: mode[html] :: member                    = sym["&#8712;"]
dform plusminus_df		: internal :: mode[html] :: plusminus                 = keyword["&plusmn;"]
dform oplus_df			: internal :: mode[html] :: oplus                     = sym["&#8853;"]
dform infty_df			: internal :: mode[html] :: infty                     = sym["&#8734;"]
dform partial_df		: internal :: mode[html] :: partial                   = sym["&#8706;"]
dform subset_df			: internal :: mode[html] :: subset                    = sym["&#8838;"]
dform supset_df			: internal :: mode[html] :: supset                    = sym["&#8839;"]
dform cap_df			: internal :: mode[html] :: cap                       = sym["&#8745;"]
dform cup_df			: internal :: mode[html] :: cup                       = sym["&#8746;"]
dform forall_df			: internal :: mode[html] :: forall                    = sym["&#8704;"]
dform exists_df			: internal :: mode[html] :: "exists"                  = sym["&#8707;"]
dform oinfty_df			: internal :: mode[html] :: oinfty                    = sym["&#8733;"]
dform shortleftrightarrow_df	: internal :: mode[html] :: shortleftrightarrow       = sym["&#8596;"]
dform shortleftarrow_df		: internal :: mode[html] :: shortleftarrow            = sym["&#8592;"]
dform shortrightarrow_df	: internal :: mode[html] :: shortrightarrow           = sym["&#8594;"]
dform longleftrightarrow_df	: internal :: mode[html] :: longleftrightarrow        = sym["&#8596;"]
dform longleftarrow_df		: internal :: mode[html] :: longleftarrow             = sym["&#8592;"]
dform longrightarrow_df		: internal :: mode[html] :: longrightarrow            = sym["&#8594;"]
dform neq_df			: internal :: mode[html] :: neq                       = sym["&#8800;"]
dform sim_df			: internal :: mode[html] :: sim                       = sym["&#8764;"]
dform le_df			: internal :: mode[html] :: le                        = sym["&#8804;"]
dform ge_df			: internal :: mode[html] :: ge                        = sym["&#8805;"]
dform equiv_df			: internal :: mode[html] :: equiv                     = sym["&#8801;"]
dform vee_df			: internal :: mode[html] :: vee                       = sym["&#8744;"]
dform leftarrow_df		: internal :: mode[html] :: leftarrow                 = sym["&#8592;"]
dform middlearrow_df		: internal :: mode[html] :: middlearrow               = sym["&#8596;"]
dform rightarrow_df		: internal :: mode[html] :: rightarrow                = sym["&#8594;"]
dform sigma_df			: internal :: mode[html] :: Sigma                     = sym["&#931;"]
dform delta_df			: internal :: mode[html] :: Delta                     = sym["&#916;"]
dform pi_df			: internal :: mode[html] :: Pi                        = sym["&#928;"]
dform times_df			: internal :: mode[html] :: times                     = keyword["&times;"]
dform div_df            	: internal :: mode[html] :: "div"                     = keyword["&divide;"]
dform supplus_df		: internal :: mode[html] :: supplus                   = sup["+"]
dform supminus_df		: internal :: mode[html] :: supminus                  = sup["-"]
dform supcirc_df		: internal :: mode[html] :: supcirc                   = keyword["&deg;"]
dform subseteq_df		: internal :: mode[html] :: subseteq                  = sym["&#8838;"]
dform supseteq_df		: internal :: mode[html] :: supseteq                  = sym["&#8839;"]
dform subzero_df		: internal :: mode[html] :: subzero                   = sub["0"]
dform subone_df			: internal :: mode[html] :: subone                    = sub["1"]
dform subtwo_df			: internal :: mode[html] :: subtwo                    = sub["2"]
dform subthree_df		: internal :: mode[html] :: subthree                  = sub["3"]
dform suba_df			: internal :: mode[html] :: suba                      = sub["a"]
dform subb_df			: internal :: mode[html] :: subb                      = sub["b"]
dform subc_df			: internal :: mode[html] :: subc                      = sub["c"]
dform subq_df			: internal :: mode[html] :: subq                      = sub["q"]
dform subz_df			: internal :: mode[html] :: subz                      = sub["z"]

dform wedge_df			: internal :: mode[tex] :: wedge                     = mathmacro["wedge"]
dform tneg_df			: internal :: mode[tex] :: tneg                      = mathmacro["neg"]
dform member_df			: internal :: mode[tex] :: member                    = mathmacro["in"]
dform plusminus_df		: internal :: mode[tex] :: plusminus                 = mathmacro["pluminus"]
dform oplus_df			: internal :: mode[tex] :: oplus                     = mathmacro["oplus"]
dform infty_df			: internal :: mode[tex] :: infty                     = mathmacro["infty"]
dform partial_df		: internal :: mode[tex] :: partial                   = mathmacro["partial"]
dform subset_df			: internal :: mode[tex] :: subset                    = mathmacro["subseteq"]
dform supset_df			: internal :: mode[tex] :: supset                    = mathmacro["supseteq"]
dform cap_df			: internal :: mode[tex] :: cap                       = mathmacro["cap"]
dform cup_df			: internal :: mode[tex] :: cup                       = mathmacro["cup"]
dform forall_df			: internal :: mode[tex] :: forall                    = mathmacro["forall"]
dform exists_df			: internal :: mode[tex] :: "exists"                  = mathmacro["exists"]
dform oinfty_df			: internal :: mode[tex] :: oinfty                    = mathmacro["oinfty"]
dform shortleftrightarrow_df	: internal :: mode[tex] :: shortleftrightarrow       = mathmacro["shortleftrightarrow"]
dform shortleftarrow_df		: internal :: mode[tex] :: shortleftarrow            = mathmacro["shortleftarrow"]
dform shortrightarrow_df	: internal :: mode[tex] :: shortrightarrow           = mathmacro["shortrightarrow"]
dform longleftrightarrow_df	: internal :: mode[tex] :: longleftrightarrow        = mathmacro["longleftrightarrow"]
dform longleftarrow_df		: internal :: mode[tex] :: longleftarrow             = mathmacro["longleftarrow"]
dform longrightarrow_df		: internal :: mode[tex] :: longrightarrow            = mathmacro["longrightarrow"]
dform neq_df			: internal :: mode[tex] :: neq                       = mathmacro["neq"]
dform sim_df			: internal :: mode[tex] :: sim                       = mathmacro["sim"]
dform le_df			: internal :: mode[tex] :: le                        = mathmacro["le"]
dform ge_df			: internal :: mode[tex] :: ge                        = mathmacro["ge"]
dform equiv_df			: internal :: mode[tex] :: equiv                     = mathmacro["equiv"]
dform vee_df			: internal :: mode[tex] :: vee                       = mathmacro["vee"]
dform leftarrow_df		: internal :: mode[tex] :: leftarrow                 = mathmacro["leftarrow"]
dform middlearrow_df		: internal :: mode[tex] :: middlearrow               = mathmacro["-"]
dform rightarrow_df		: internal :: mode[tex] :: rightarrow                = mathmacro["rightarrow"]
dform sigma_df			: internal :: mode[tex] :: Sigma                     = mathmacro["Sigma"]
dform delta_df			: internal :: mode[tex] :: Delta                     = mathmacro["Delta"]
dform pi_df			: internal :: mode[tex] :: Pi                        = mathmacro["Pi"]
dform times_df			: internal :: mode[tex] :: times                     = mathmacro["times"]
dform div_df            	: internal :: mode[tex] :: "div"                     = mathmacro["div"]
dform supplus_df		: internal :: mode[tex] :: supplus                   = ensuremath["^{+}"]
dform supminus_df		: internal :: mode[tex] :: supminus                  = ensuremath["^{-}"]
dform supcirc_df		: internal :: mode[tex] :: supcirc                   = ensuremath["^{\circ}"]
dform subseteq_df		: internal :: mode[tex] :: subseteq                  = mathmacro["subseteq"]
dform supseteq_df		: internal :: mode[tex] :: supseteq                  = mathmacro["supseteq"]
dform subzero_df		: internal :: mode[tex] :: subzero                   = ensuremath["_0"]
dform subone_df			: internal :: mode[tex] :: subone                    = ensuremath["_1"]
dform subtwo_df			: internal :: mode[tex] :: subtwo                    = ensuremath["_2"]
dform subthree_df		: internal :: mode[tex] :: subthree                  = ensuremath["_3"]
dform suba_df			: internal :: mode[tex] :: suba                      = ensuremath["_a"]
dform subb_df			: internal :: mode[tex] :: subb                      = ensuremath["_b"]
dform subc_df			: internal :: mode[tex] :: subc                      = ensuremath["_c"]
dform subq_df			: internal :: mode[tex] :: subq                      = ensuremath["_q"]
dform subz_df			: internal :: mode[tex] :: subz                      = ensuremath["_z"]

(*
 * -*-
 * Local Variables: internal ::
 * Caml-master: "htmlcomp.run"
 * End:
 * -*-
 *)
