(*
 * characters in the Nuprl font.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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
open Nl_debug

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Nuprl_font%t" eflush

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

(* Displays *)
dform mathbbA_df		: mode[prl] :: mathbbA                   = `"\129"
dform mathbbB_df		: mode[prl] :: mathbbB                   = `"\130"
dform mathbbC_df		: mode[prl] :: mathbbC                   = `"\131"
dform mathbbD_df		: mode[prl] :: mathbbD                   = `"\132"
dform mathbbE_df		: mode[prl] :: mathbbE                   = `"\133"
dform mathbbF_df		: mode[prl] :: mathbbF                   = `"\134"
dform mathbbG_df		: mode[prl] :: mathbbG                   = `"\135"
dform mathbbH_df		: mode[prl] :: mathbbH                   = `"\136"
dform mathbbI_df		: mode[prl] :: mathbbI                   = `"\137"
dform mathbbJ_df		: mode[prl] :: mathbbJ                   = `"\138"
dform mathbbK_df		: mode[prl] :: mathbbK                   = `"\139"
(* dform mathbbL_df		: mode[prl] :: mathbbL                   = `"\140" *)
dform mathbbM_df		: mode[prl] :: mathbbN                   = `"\141"
dform mathbbN_df		: mode[prl] :: mathbbO                   = `"\142"
dform mathbbO_df		: mode[prl] :: mathbbP                   = `"\143"
dform mathbbP_df		: mode[prl] :: mathbbQ                   = `"\144"
dform mathbbQ_df		: mode[prl] :: mathbbR                   = `"\145"
dform mathbbR_df		: mode[prl] :: mathbbS                   = `"\146"
dform mathbbS_df		: mode[prl] :: mathbbT                   = `"\147"
dform mathbbT_df		: mode[prl] :: mathbbU                   = `"\148"
dform mathbbU_df		: mode[prl] :: mathbbV                   = `"\149"
dform mathbbV_df		: mode[prl] :: mathbbW                   = `"\150"
dform mathbbW_df		: mode[prl] :: mathbbX                   = `"\151"
dform mathbbX_df		: mode[prl] :: mathbbY                   = `"\152"
dform mathbbY_df		: mode[prl] :: mathbbZ                   = `"\153"

dform shortLeftarrow_df		: mode[prl] :: shortLeftarrow            = `"\1565"
dform leftarrow_df		: mode[prl] :: Leftarrow                 = `"\220\221"
dform middlearrow_df		: mode[prl] :: Middlearrow               = `"\221"
dform shortRightarrow_df	: mode[prl] :: shortRightarrow           = `"\158"
dform rightarrow_df		: mode[prl] :: Rightarrow                = `"\157\158"
dform leftrightarrow_df		: mode[prl] :: Leftrightarrow            = `"\220\221\222"
dform ulcorner_df		: mode[prl] :: ulcorner                  = `"\154"
dform urcorner_df		: mode[prl] :: urcorner                  = `"\155"
dform vdash_df                  : mode[prl] :: vdash                     = `"\159"
dform integral_df		: mode[prl] :: integral                  = `"\160"
dform cdot_df                   : mode[prl] :: cdot                      = `"\204"
dform downarrow_df		: mode[prl] :: downarrow                 = `"\205"
dform uparrow_df		: mode[prl] :: uparrow                   = `"\206"
dform alpha_df                  : mode[prl] :: alpha                     = `"\161"
dform beta_df			: mode[prl] :: beta                      = `"\162"
dform pi_df			: mode[prl] :: pi                        = `"\176"
dform lambda_df			: mode[prl] :: lambda                    = `"\171"
dform gamma_df			: mode[prl] :: gamma                     = `"\163"
dform delta_df			: mode[prl] :: delta                     = `"\164"
dform rho_df			: mode[prl] :: rho                       = `"\177"
dform sigma_df			: mode[prl] :: sigma                     = `"\178"
dform epsilon_df		: mode[prl] :: epsilon                   = `"\165"
dform eta_df			: mode[prl] :: eta                       = `"\167"
dform theta_df			: mode[prl] :: theta                     = `"\168"
dform iota_df			: mode[prl] :: iota                      = `"\169"
dform kappa_df			: mode[prl] :: kappa                     = `"\170"
dform mu_df			: mode[prl] :: mu                        = `"\172"
dform nu_df			: mode[prl] :: nu                        = `"\173"
dform omicron_df		: mode[prl] :: omicron                   = `"\175"
dform tau_df			: mode[prl] :: tau                       = `"\179"
dform phi_df			: mode[prl] :: phi                       = `"\181"
dform xi_df			: mode[prl] :: xi                        = `"\182"
dform omega_df			: mode[prl] :: omega                     = `"\184"

dform wedge_df			: mode[prl] :: wedge                     = `"\207"
dform tneg_df			: mode[prl] :: tneg                      = `"\191"
dform member_df			: mode[prl] :: member                    = `"\209"
dform plusminus_df		: mode[prl] :: plusminus                 = `"\210"
dform oplus_df			: mode[prl] :: oplus                     = `"XXX"
dform infty_df			: mode[prl] :: infty                     = `"XXX"
dform partial_df		: mode[prl] :: partial                   = `"\211"
dform subset_df			: mode[prl] :: subset                    = `"\212"
dform supset_df			: mode[prl] :: supset                    = `"\213"
dform cap_df			: mode[prl] :: cap                       = `"\214"
dform cup_df			: mode[prl] :: cup                       = `"\215"
dform forall_df			: mode[prl] :: forall                    = `"\216"
dform exists_df			: mode[prl] :: "exists"                  = `"\217"
dform oinfty_df			: mode[prl] :: oinfty                    = `"XXX"
dform shortleftrightarrow_df	: mode[prl] :: shortleftrightarrow       = `"\165"
dform shortleftarrow_df		: mode[prl] :: shortleftarrow            = `"\220"
dform shortrightarrow_df	: mode[prl] :: shortrightarrow           = `"\222"
dform longleftrightarrow_df	: mode[prl] :: longleftrightarrow        = `"\223\221\221\222"
dform longleftarrow_df		: mode[prl] :: longleftarrow             = `"\220\221\221"
dform longrightarrow_df		: mode[prl] :: longrightarrow            = `"\221\221\222"
dform neq_df			: mode[prl] :: neq                       = `"225"
dform sim_df			: mode[prl] :: sim                       = `"XXX"
dform le_df			: mode[prl] :: le                        = `"\218"
dform ge_df			: mode[prl] :: ge                        = `"\219"
dform equiv_df			: mode[prl] :: equiv                     = `"\226"
dform vee_df			: mode[prl] :: vee                       = `"\208"
dform leftarrow_df		: mode[prl] :: leftarrow                 = `"\223\221"
dform middlearrow_df		: mode[prl] :: middlearrow               = `"\221"
dform rightarrow_df		: mode[prl] :: rightarrow                = `"\221\222"
dform sigma_df			: mode[prl] :: Sigma                     = `"\199"
dform delta_df			: mode[prl] :: Delta                     = `"\194"
dform pi_df			: mode[prl] :: Pi                        = `"\198"
dform times_df			: mode[prl] :: times                     = `"\227"
dform div_df            	: mode[prl] :: "div"                     = `"\228"
dform supplus_df		: mode[prl] :: supplus                   = `"\229"
dform supminus_df		: mode[prl] :: supminus                  = `"\230"
dform supcirc_df		: mode[prl] :: supcirc                   = `"\231"
dform subseteq_df		: mode[prl] :: subseteq                  = `"\232"
dform supseteq_df		: mode[prl] :: supseteq                  = `"\233"
dform subzero_df		: mode[prl] :: subzero                   = `"\240"
dform subone_df			: mode[prl] :: subone                    = `"\241"
dform subtwo_df			: mode[prl] :: subtwo                    = `"\242"
dform subthree_df		: mode[prl] :: subthree                  = `"\244"
dform suba_df			: mode[prl] :: suba                      = `"\237"
dform subb_df			: mode[prl] :: subb                      = `"\236"
dform subc_df			: mode[prl] :: subc                      = `"\238"
dform subq_df			: mode[prl] :: subq                      = `"XXX"
dform subz_df			: mode[prl] :: subz                      = `"\235"

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
