(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define and implement operations for ML ints in the FIR.
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
 * Author: Brian Emre Aydemir
 * Email:  emre@its.caltech.edu
 *)

include Base_theory
include Itt_theory
include Fir_ty
include Fir_exp

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

(* Max / min. *)
declare maxIntOp
declare minIntOp

(* Boolean comparisons. *)
declare eqIntOp
declare neqIntOp
declare ltIntOp
declare leIntOp
declare gtIntOp
declare geIntOp
declare cmpIntOp

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

(* Max / min. *)
dform maxIntOp_df : except_mode[src] :: maxIntOp = `"max"
dform minIntOp_df : except_mode[src] :: minIntOp = `"min"

(* Comparison. *)
dform eqIntOp_df : except_mode[src] :: eqIntOp = `"="
dform neqIntOp_df : except_mode[src] :: neqIntOp = `"!="
dform ltIntOp_df : except_mode[src] :: ltIntOp = `"<"
dform leIntOp_df : except_mode[src] :: leIntOp = Nuprl_font!le
dform gtIntOp_df : except_mode[src] :: gtIntOp = `">"
dform geIntOp_df : except_mode[src] :: geIntOp = Nuprl_font!ge
dform cmpIntOp_df : except_mode[src] :: cmpIntOp = `"compare"

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Unary and bitwise negation. *)
prim_rw reduce_uminusIntOp :
   unop_exp{ uminusIntOp; 'a1 } <-->
   "minus"{'a1}

(* Standard binary arithmetic operators. *)
prim_rw reduce_plusIntOp :
   binop_exp{ plusIntOp; 'a1; 'a2 } <-->
   ('a1 +@ 'a2)
prim_rw reduce_minusIntOp :
   binop_exp{ minusIntOp; 'a1; 'a2 } <-->
   ('a1 -@ 'a2)
prim_rw reduce_mulIntOp :
   binop_exp{ mulIntOp; 'a1; 'a2 } <-->
   ('a1 *@ 'a2)
prim_rw reduce_divIntOp :
   binop_exp{ divIntOp; 'a1; 'a2 } <-->
   ('a1 /@ 'a2)
prim_rw reduce_remIntOp :
   binop_exp{ remIntOp; 'a1; 'a2 } <-->
   ('a1 %@ 'a2)

(* Binary bitwise operators. *)

(*
 * Nothing as of yet.
 *)

(* Max / min. *)
prim_rw reduce_maxIntOp :
   binop_exp{ maxIntOp; 'a1; 'a2 } <-->
   ifthenelse{ lt_bool{'a1; 'a2}; 'a2; 'a1 }
prim_rw reduce_minIntOp :
   binop_exp{ minIntOp; 'a1; 'a2 } <-->
   ifthenelse{ lt_bool{'a1; 'a2}; 'a1; 'a2 }

(* Boolean comparisons. *)
prim_rw reduce_eqIntOp :
   binop_exp{ eqIntOp; 'a1; 'a2 } <-->
   ifthenelse{ beq_int{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_neqIntOp :
   binop_exp{ neqIntOp; 'a1; 'a2 } <-->
   ifthenelse{ bneq_int{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_ltIntOp :
   binop_exp{ ltIntOp; 'a1; 'a2 } <-->
   ifthenelse{ lt_bool{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_leIntOp :
   binop_exp{ leIntOp; 'a1; 'a2 } <-->
   ifthenelse{ le_bool{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_gtIntOp :
   binop_exp{ gtIntOp; 'a1; 'a2 } <-->
   ifthenelse{ gt_bool{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_geIntOp :
   binop_exp{ geIntOp; 'a1; 'a2 } <-->
   ifthenelse{ ge_bool{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_cmpIntOp :
   binop_exp{ cmpIntOp; 'a1; 'a2 } <-->
   ifthenelse{ beq_int{'a1; 'a2};
      0;
      ifthenelse{ lt_bool{'a1; 'a2};
         (-1);
         1
      }
   }

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << unop_exp{ uminusIntOp; 'a1 } >>, reduce_uminusIntOp;
   << binop_exp{ plusIntOp; 'a1; 'a2 } >>, reduce_plusIntOp;
   << binop_exp{ minusIntOp; 'a1; 'a2 } >>, reduce_minusIntOp;
   << binop_exp{ mulIntOp; 'a1; 'a2 } >>, reduce_mulIntOp;
   << binop_exp{ divIntOp; 'a1; 'a2 } >>, reduce_divIntOp;
   << binop_exp{ remIntOp; 'a1; 'a2 } >>, reduce_remIntOp;
   << binop_exp{ maxIntOp; 'a1; 'a2 } >>, reduce_maxIntOp;
   << binop_exp{ minIntOp; 'a1; 'a2 } >>, reduce_minIntOp;
   << binop_exp{ eqIntOp; 'a1; 'a2 } >>, reduce_eqIntOp;
   << binop_exp{ neqIntOp; 'a1; 'a2 } >>, reduce_neqIntOp;
   << binop_exp{ ltIntOp; 'a1; 'a2 } >>, reduce_ltIntOp;
   << binop_exp{ leIntOp; 'a1; 'a2 } >>, reduce_leIntOp;
   << binop_exp{ gtIntOp; 'a1; 'a2 } >>, reduce_gtIntOp;
   << binop_exp{ geIntOp; 'a1; 'a2 } >>, reduce_geIntOp;
   << binop_exp{ cmpIntOp; 'a1; 'a2 } >>, reduce_cmpIntOp
]
