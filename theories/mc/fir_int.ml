(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define and implement operations for ML ints in the FIR.
 * See fir_int.mli for a description of what the operators below do.
 *
 * Todo:
 *    -  Complete the implementation of the bitwise operators.
 *)

include Itt_theory
include Fir_exp

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Unary and bitwise negation. *)
declare uminusIntOp
declare notIntOp

(* Standard binary arithmetic operators. *)
declare plusIntOp
declare minusIntOp
declare mulIntOp
declare divIntOp
declare remIntOp

(* Binary bitwise operators. *)
declare lslIntOp
declare lsrIntOp
declare asrIntOp
declare andIntOp
declare orIntOp
declare xorIntOp

(* Boolean comparisons. *)
declare eqIntOp
declare neqIntOp
declare ltIntOp
declare leIntOp
declare gtIntOp
declare geIntOp

(* Exponentiation assuming a non-negative, integral exponent. *)
define unfold_pow : pow{ 'base; 'exp } <-->
   ind{ 'exp; i, j. 1; 1; i, j. "mul"{'base; 'j} }

(*************************************************************************
 * Display forms.
 * Use C-style notation for the bitwise operators.
 *************************************************************************)

(* Unary and bitwise negation. *)
dform uminusIntOp_df : except_mode[src] :: uminusIntOp = `"-"
dform notIntOp_df : except_mode[src] :: notIntOp = `"~"

(* Standard binary arithmetic operators. *)
dform plusIntOp_df : except_mode[src] :: plusIntOp = `"+"
dform minusIntOp_df : except_mode[src] :: minusIntOp = `"-"
dform mulIntOp_df : except_mode[src] :: mulIntOp = `"*"
dform divIntOp_df : except_mode[src] :: divIntOp = Nuprl_font!"div"
dform remIntOp_df : except_mode[src] :: remIntOp = `"rem"

(* Binary bitwise oerators. *)
dform lslIntOp_df : except_mode[src] :: lslIntOp = `"<<"
dform lsrIntOp_df : except_mode[src] :: lsrIntOp = `">>"
dform asrIntOp_df : except_mode[src] :: asrIntOp = `">>"
dform andIntOp_df : except_mode[src] :: andIntOp = `"&"
dform orIntOp_df  : except_mode[src] :: orIntOp  = `"|"
dform xorIntOp_df : except_mode[src] :: xorIntOp = `"^"

(* Comparison. *)
dform eqIntOp_df : except_mode[src] :: eqIntOp = `"="
dform neqIntOp_df : except_mode[src] :: neqIntOp = `"!="
dform ltIntOp_df : except_mode[src] :: ltIntOp = `"<"
dform leIntOp_df : except_mode[src] :: leIntOp = Nuprl_font!le
dform gtIntOp_df : except_mode[src] :: gtIntOp = `">"
dform geIntOp_df : except_mode[src] :: geIntOp = Nuprl_font!ge

(* Exponentiation. *)
dform pow_df : except_mode[src] :: pow{ 'base; 'exp } =
   lzone `"(" slot{'base} `"^" slot{'exp} `")" ezone

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Unary and bitwise negation. *)
prim_rw reduce_uminusIntOp : unOp{ uminusIntOp; 'a1; v. 'exp['v] } <-->
   'exp[ "minus"{'a1} ]
(* prim_rw reduce_notIntOp : unOp{ notIntOp; 'a1; v. 'exp['v] } <--> *)

(* Standard binary arithmetic operators. *)
prim_rw reduce_plusIntOp : binOp{ plusIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ('a1 +@ 'a2) ]
prim_rw reduce_minusIntOp : binOp{ minusIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ('a1 -@ 'a2) ]
prim_rw reduce_mulIntOp : binOp{ mulIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ('a1 *@ 'a2) ]
prim_rw reduce_divIntOp : binOp{ divIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ('a1 /@ 'a2) ]
prim_rw reduce_remIntOp : binOp{ remIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ('a1 %@ 'a2) ]

(* Binary bitwise operators. *)
prim_rw reduce_lslIntOp : binOp{ lslIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ( 'a1 *@ pow{2; 'a2} ) ]
prim_rw reduce_lsrIntOp : binOp{ lsrIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ( 'a1 /@ pow{2; 'a2} ) ]
prim_rw reduce_asrIntOp : binOp{ asrIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ( 'a1 /@ pow{2; 'a2} ) ]
(*prim_rw reduce_andIntOp : binOp{ andIntOp; 'a1; 'a2; v. 'exp['v] } <-->
prim_rw reduce_orIntOp : binOp{ orIntOp; 'a1; 'a2; v. 'exp['v] } <-->
prim_rw reduce_xorIntOp : binOp{ xorIntOp; 'a1; 'a2; v. 'exp['v] } <-->*)

(* Comparison. *)
prim_rw reduce_eqIntOp : binOp{ eqIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ifthenelse{ beq_int{ 'a1; 'a2 }; ftrue; ffalse } ]
prim_rw reduce_neqIntOp : binOp{ neqIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ifthenelse{ bneq_int{ 'a1; 'a2 }; ftrue; ffalse } ]
prim_rw reduce_ltIntOp : binOp{ ltIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ifthenelse{ lt_bool{ 'a1; 'a2 }; ftrue; ffalse } ]
prim_rw reduce_leIntOp : binOp{ leIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ifthenelse{ le_bool{ 'a1; 'a2 }; ftrue; ffalse } ]
prim_rw reduce_gtIntOp : binOp{ gtIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ifthenelse{ gt_bool{ 'a1; 'a2 }; ftrue; ffalse } ]
prim_rw reduce_geIntOp : binOp{ geIntOp; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ ifthenelse{ ge_bool{ 'a1; 'a2 }; ftrue; ffalse } ]

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << unOp{ uminusIntOp; 'a1; v. 'exp['v] } >>, reduce_uminusIntOp;
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
   << binOp{ neqIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_neqIntOp;
   << binOp{ ltIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_ltIntOp;
   << binOp{ leIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_leIntOp;
   << binOp{ gtIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_gtIntOp;
   << binOp{ geIntOp; 'a1; 'a2; v. 'exp['v] } >>, reduce_geIntOp;

   << pow{ 'base; 'exp } >>, unfold_pow
]
