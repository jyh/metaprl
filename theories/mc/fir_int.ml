(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define and implement operations for ML ints.
 * See fir_int.mli for a description of what the operators below do.
 *
 * Todo:
 *    - implement the bitwise operators.  this could be a pain.
 *    - check that the implementation is correct and that it
 *      conforms to the description in fir_int.mli
 *    - once I can actually get div and rem to eval properly,
 *      I should be able to properly do the bitwise operators.
 *)

include Itt_theory
include Fir_exp

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

declare uminusIntOp
declare notIntOp

declare plusIntOp
declare minusIntOp
declare mulIntOp
declare divIntOp
declare remIntOp

declare lslIntOp
declare lsrIntOp
declare asrIntOp
declare andIntOp
declare orIntOp
declare xorIntOp

declare eqIntOp
declare ltIntOp
declare leIntOp
declare gtIntOp
declare geIntOp

(* Exponentiation, assuming a non-negative exponent. *)
define unfold_pow : pow{ 'base; 'exp } <-->
   ind{ 'exp; i, j. 1; 1; i, j. "mul"{'base; 'j} }

(*************************************************************************
 * Display forms.
 * Use C-style notation for the bitwise operators.
 *************************************************************************)

dform uminusIntOp_df : uminusIntOp = `"-"
dform notIntOp_df : notIntOp = `"~"

dform plusIntOp_df : plusIntOp = `"+"
dform minusIntOp_df : minusIntOp = `"-"
dform mulIntOp_df : mulIntOp = `"*"
dform divIntOp_df : divIntOp = Nuprl_font!"div"
dform remIntOp_df : remIntOp = `"rem"

dform lslIntOp_df : lslIntOp = `"<<"
dform lsrIntOp_df : lsrIntOp = `">>"
dform asrIntOp_df : asrIntOp = `">>"
dform andIntOp_df : andIntOp = `"&"
dform orIntOp_df  : orIntOp  = `"|"
dform xorIntOp_df : xorIntOp = `"^"

dform eqIntOp_df : eqIntOp = `"="
dform ltIntOp_df : ltIntOp = `"<"
dform leIntOp_df : leIntOp = Nuprl_font!"le"
dform gtIntOp_df : gtIntOp = `">"
dform geIntOp_df : geIntOp = Nuprl_font!"ge"

dform pow_df : pow{ 'base; 'exp } =
   lzone `"(" slot{'base} `"^" slot{'exp} `")" ezone

(*************************************************************************
 * Rewrites.
 *************************************************************************)

prim_rw reduce_uminusIntOp : unOp{ uminusIntOp; 'a1; v. 'exp['v] } <-->
   'exp[ "sub"{ 0; 'a1} ]
(* prim_rw reduce_notIntOp : unOp{ notIntOp; 'a1; v. 'exp['v] } <--> *)

prim_rw reduce_plusIntOp : binOp{ plusIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ "add"{'a1; 'a2} ]
prim_rw reduce_minusIntOp : binOp{ minusIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ "sub"{'a1; 'a2} ]
prim_rw reduce_mulIntOp : binOp{ mulIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ "mul"{'a1; 'a2} ]
prim_rw reduce_divIntOp : binOp{ divIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ "div"{'a1; 'a2} ]
prim_rw reduce_remIntOp : binOp{ remIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ "rem"{'a1; 'a2} ]

(* See fir_int.mli concerning the implementation of the shift operators. *)
prim_rw reduce_lslIntOp : binOp{ lslIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ "mul"{ 'a1; pow{ 2; 'a2}} ]
prim_rw reduce_lsrIntOp : binOp{ lsrIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ "div"{ 'a1; pow{ 2; 'a2}} ]
prim_rw reduce_asrIntOp : binOp{ asrIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ "div"{ 'a1; pow{ 2; 'a2}} ]
(*prim_rw reduce_andIntOp : binOp{ andIntOp; 'a1; 'a2; v. 'exp['v] } <-->
prim_rw reduce_orIntOp : binOp{ orIntOp; 'a1; 'a2; v. 'exp['v] } <-->
prim_rw reduce_xorIntOp : binOp{ xorIntOp; 'a1; 'a2; v. 'exp['v] } <-->*)

prim_rw reduce_eqIntOp : binOp{ eqIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ eq_int{'a1; 'a2} ]
prim_rw reduce_ltIntOp : binOp{ ltIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ lt_int{'a1; 'a2} ]
prim_rw reduce_leIntOp : binOp{ leIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ le_int{'a1; 'a2} ]
prim_rw reduce_gtIntOp : binOp{ gtIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ gt_int{'a1; 'a2} ]
prim_rw reduce_geIntOp : binOp{ geIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ge_int{'a1; 'a2} ]

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce +=
   [<< unOp{ uminusIntOp; 'a1; v. 'exp['v] } >>, reduce_uminusIntOp;
    (*<< unOpr{ notIntOp; 'a1; v. 'exp['v] } >>, reduce_notIntOp;*)

    << binOp{ plusIntOp; 'a1; 'a2; v. 'exp['v] } >>,  reduce_plusIntOp;
    << binOp{ minusIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_minusIntOp;
    << binOp{ mulIntOp; 'a1; 'a2; v. 'exp['v] } >>,   reduce_mulIntOp;
    << binOp{ divIntOp; 'a1; 'a2; v. 'exp['v] } >>,   reduce_divIntOp;
    << binOp{ remIntOp; 'a1; 'a2; v. 'exp['v] } >>,   reduce_remIntOp;

    << binOp{ lslIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_lslIntOp;
    << binOp{ lsrIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_lsrIntOp;
    << binOp{ asrIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_asrIntOp;
    (*<< binOp{ andIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_andIntOp;
    << binOp{ orIntOp; 'a1; 'a2; v. 'exp['v] } >>,  reduce_orIntOp;
    << binOp{ xorIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_xorIntOp;*)

    << binOp{ eqIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_eqIntOp;
    << binOp{ ltIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_ltIntOp;
    << binOp{ leIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_leIntOp;
    << binOp{ gtIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_gtIntOp;
    << binOp{ geIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_geIntOp;

    << pow{ 'base; 'exp } >>, unfold_pow]

(*************************************************************************
 * Scratch space...
 *************************************************************************)


