(*
 * characters in the Nuprl font.
 *
 * $Log$
 * Revision 1.5  1998/04/29 20:53:48  jyh
 * Initial working display forms.
 *
 * Revision 1.4  1998/04/24 19:39:09  jyh
 * Updated debugging.
 *
 * Revision 1.3  1998/04/24 02:43:15  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.2  1998/04/17 01:31:25  jyh
 * Editor is almost constructed.
 *
 * Revision 1.1  1997/04/28 15:51:56  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.2  1996/05/21 02:16:16  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.1  1996/04/11 13:33:29  jyh
 * This is the final version with the old syntax for terms.
 *
 *)

open Printf
open Debug

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Nuprl_font%t" eflush

(* Displays *)
declare mathbbP
declare mathbbR
declare mathbbN
declare mathbbC
declare mathbbQ
declare mathbbZ
declare mathbbU
declare mathbbB
declare shortLeftarrow
declare Leftarrow
declare Middlearrow
declare shortRightarrow
declare Rightarrow
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
dform mathbbP_df		: mode[prl] :: mathbbP                   = `"\128"
dform mathbbR_df		: mode[prl] :: mathbbR                   = `"\129"
dform mathbbN_df		: mode[prl] :: mathbbN                   = `"\130"
dform mathbbC_df		: mode[prl] :: mathbbC                   = `"\131"
dform mathbbQ_df		: mode[prl] :: mathbbQ                   = `"\132"
dform mathbbZ_df		: mode[prl] :: mathbbZ                   = `"\133"
dform mathbbU_df		: mode[prl] :: mathbbU                   = `"\134"
dform mathbbB_df		: mode[prl] :: mathbbB                   = `"\192"
dform shortLeftarrow_df		: mode[prl] :: shortLeftarrow            = `"\135"
dform leftarrow_df		: mode[prl] :: Leftarrow                 = `"\135\136"
dform middlearrow_df		: mode[prl] :: Middlearrow               = `"\136"
dform shortRightarrow_df	: mode[prl] :: shortRightarrow           = `"\137"
dform rightarrow_df		: mode[prl] :: Rightarrow                = `"\136\137"
dform ulcorner_df		: mode[prl] :: ulcorner                  = `"\138"
dform urcorner_df		: mode[prl] :: urcorner                  = `"\139"
dform vdash_df                  : mode[prl] :: vdash                     = `"\140"
dform integral_df		: mode[prl] :: integral                  = `"\141"
dform cdot_df                   : mode[prl] :: cdot                      = `"\142"
dform downarrow_df		: mode[prl] :: downarrow                 = `"\143"
dform uparrow_df		: mode[prl] :: uparrow                   = `"\162"
dform alpha_df                  : mode[prl] :: alpha                     = `"\144"
dform beta_df			: mode[prl] :: beta                      = `"\145"
dform pi_df			: mode[prl] :: pi                        = `"\146"
dform lambda_df			: mode[prl] :: lambda                    = `"\150"
dform gamma_df			: mode[prl] :: gamma                     = `"\151"
dform delta_df			: mode[prl] :: delta                     = `"\152"
dform rho_df			: mode[prl] :: rho                       = `"\193"
dform wedge_df			: mode[prl] :: wedge                     = `"\146"
dform tneg_df			: mode[prl] :: tneg                      = `"\147"
dform member_df			: mode[prl] :: member                    = `"\148"
dform plusminus_df		: mode[prl] :: plusminus                 = `"\154"
dform oplus_df			: mode[prl] :: oplus                     = `"\155"
dform infty_df			: mode[prl] :: infty                     = `"\156"
dform partial_df		: mode[prl] :: partial                   = `"\157"
dform subset_df			: mode[prl] :: subset                    = `"\158"
dform supset_df			: mode[prl] :: supset                    = `"\159"
dform cap_df			: mode[prl] :: cap                       = `"\160"
dform cup_df			: mode[prl] :: cup                       = `"\161"
dform forall_df			: mode[prl] :: forall                    = `"\162"
dform _df			: mode[prl] :: "exists"                  = `"\163"
dform oinfty_df			: mode[prl] :: oinfty                    = `"\164"
dform shortleftrightarrow_df	: mode[prl] :: shortleftrightarrow       = `"\165"
dform shortleftarrow_df		: mode[prl] :: shortleftarrow            = `"\166"
dform shortrightarrow_df	: mode[prl] :: shortrightarrow           = `"\167"
dform longleftrightarrow_df	: mode[prl] :: longleftrightarrow        = `"\135\136\136\137"
dform longleftarrow_df		: mode[prl] :: longleftarrow             = `"\135\136\136"
dform longrightarrow_df		: mode[prl] :: longrightarrow            = `"\136\136\137"
dform neq_df			: mode[prl] :: neq                       = `"\168"
dform sim_df			: mode[prl] :: sim                       = `"\169"
dform le_df			: mode[prl] :: le                        = `"\170"
dform ge_df			: mode[prl] :: ge                        = `"\171"
dform equiv_df			: mode[prl] :: equiv                     = `"\172"
dform vee_df			: mode[prl] :: vee                       = `"\173"
dform leftarrow_df		: mode[prl] :: leftarrow                 = `"\174\175"
dform middlearrow_df		: mode[prl] :: middlearrow               = `"\175"
dform rightarrow_df		: mode[prl] :: rightarrow                = `"\175\176"
dform sigma_df			: mode[prl] :: Sigma                     = `"\177"
dform delta_df			: mode[prl] :: Delta                     = `"\178"
dform pi_df			: mode[prl] :: Pi                        = `"\179"
dform times_df			: mode[prl] :: times                     = `"\180"
dform div_df            	: mode[prl] :: "div"                     = `"\181"
dform supplus_df		: mode[prl] :: supplus                   = `"\182"
dform supminus_df		: mode[prl] :: supminus                  = `"\183"
dform supcirc_df		: mode[prl] :: supcirc                   = `"\184"
dform subseteq_df		: mode[prl] :: subseteq                  = `"\185"
dform supseteq_df		: mode[prl] :: supseteq                  = `"\186"
dform subzero_df		: mode[prl] :: subzero                   = `"\187"
dform subone_df			: mode[prl] :: subone                    = `"\188"
dform subtwo_df			: mode[prl] :: subtwo                    = `"\189"
dform subthree_df		: mode[prl] :: subthree                  = `"\190"
dform suba_df			: mode[prl] :: suba                      = `"\194"
dform subb_df			: mode[prl] :: subb                      = `"\196"
dform subc_df			: mode[prl] :: subc                      = `"\198"
dform subq_df			: mode[prl] :: subq                      = `"\195"
dform subz_df			: mode[prl] :: subz                      = `"\197"

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
