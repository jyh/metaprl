(*
 * characters in the Nuprl font.
 *
 * $Log$
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
dform mode[prl] :: mathbbP                   = `"\128"
dform mode[prl] :: mathbbR                   = `"\129"
dform mode[prl] :: mathbbN                   = `"\130"
dform mode[prl] :: mathbbC                   = `"\131"
dform mode[prl] :: mathbbQ                   = `"\132"
dform mode[prl] :: mathbbZ                   = `"\133"
dform mode[prl] :: mathbbU                   = `"\134"
dform mode[prl] :: mathbbB                   = `"\192"
dform mode[prl] :: shortLeftarrow            = `"\135"
dform mode[prl] :: Leftarrow                 = `"\135\136"
dform mode[prl] :: Middlearrow               = `"\136"
dform mode[prl] :: shortRightarrow           = `"\137"
dform mode[prl] :: Rightarrow                = `"\136\137"
dform mode[prl] :: ulcorner                  = `"\138"
dform mode[prl] :: urcorner                  = `"\139"
dform mode[prl] :: vdash                     = `"\140"
dform mode[prl] :: integral                  = `"\141"
dform mode[prl] :: cdot                      = `"\142"
dform mode[prl] :: downarrow                 = `"\143"
dform mode[prl] :: uparrow                   = `"\162"
dform mode[prl] :: alpha                     = `"\144"
dform mode[prl] :: beta                      = `"\145"
dform mode[prl] :: pi                        = `"\146"
dform mode[prl] :: lambda                    = `"\150"
dform mode[prl] :: gamma                     = `"\151"
dform mode[prl] :: delta                     = `"\152"
dform mode[prl] :: rho                       = `"\193"
dform mode[prl] :: wedge                     = `"\146"
dform mode[prl] :: tneg                      = `"\147"
dform mode[prl] :: member                    = `"\148"
dform mode[prl] :: plusminus                 = `"\154"
dform mode[prl] :: oplus                     = `"\155"
dform mode[prl] :: infty                     = `"\156"
dform mode[prl] :: partial                   = `"\157"
dform mode[prl] :: subset                    = `"\158"
dform mode[prl] :: supset                    = `"\159"
dform mode[prl] :: cap                       = `"\160"
dform mode[prl] :: cup                       = `"\161"
dform mode[prl] :: forall                    = `"\162"
dform mode[prl] :: "exists"                  = `"\163"
dform mode[prl] :: oinfty                    = `"\164"
dform mode[prl] :: shortleftrightarrow       = `"\165"
dform mode[prl] :: shortleftarrow            = `"\166"
dform mode[prl] :: shortrightarrow           = `"\167"
dform mode[prl] :: longleftrightarrow        = `"\135\136\136\137"
dform mode[prl] :: longleftarrow             = `"\135\136\136"
dform mode[prl] :: longrightarrow            = `"\136\136\137"
dform mode[prl] :: neq                       = `"\168"
dform mode[prl] :: sim                       = `"\169"
dform mode[prl] :: le                        = `"\170"
dform mode[prl] :: ge                        = `"\171"
dform mode[prl] :: equiv                     = `"\172"
dform mode[prl] :: vee                       = `"\173"
dform mode[prl] :: leftarrow                 = `"\174\175"
dform mode[prl] :: middlearrow               = `"\175"
dform mode[prl] :: rightarrow                = `"\175\176"
dform mode[prl] :: Sigma                     = `"\177"
dform mode[prl] :: Delta                     = `"\178"
dform mode[prl] :: Pi                        = `"\179"
dform mode[prl] :: times                     = `"\180"
dform mode[prl] :: "div"                     = `"\181"
dform mode[prl] :: supplus                   = `"\182"
dform mode[prl] :: supminus                  = `"\183"
dform mode[prl] :: supcirc                   = `"\184"
dform mode[prl] :: subseteq                  = `"\185"
dform mode[prl] :: supseteq                  = `"\186"
dform mode[prl] :: subzero                   = `"\187"
dform mode[prl] :: subone                    = `"\188"
dform mode[prl] :: subtwo                    = `"\189"
dform mode[prl] :: subthree                  = `"\190"
dform mode[prl] :: suba                      = `"\194"
dform mode[prl] :: subb                      = `"\196"
dform mode[prl] :: subc                      = `"\198"
dform mode[prl] :: subq                      = `"\195"
dform mode[prl] :: subz                      = `"\197"

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
