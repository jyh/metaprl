(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define how to evaluate the FIR in MetaPRL.
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

include Fir_int_set
include Fir_ty
include Fir_exp
include Itt_list2

open Top_conversionals
open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Boolean type.
 *)

declare true_set
declare false_set
declare val_true
declare val_false

(*
 * Functions.
 *)

declare lambda{ x. 'f['x] }   (* for functions with >= 1 arguments *)
declare lambda{ 'f }          (* function with no arguments *)
declare apply{ 'f; 'x }
declare fix{ f. 'b['f] }

(*
 * Misc.
 *)

declare unknownFun

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Boolean type *)
dform true_set_df : except_mode[src] :: true_set = `"true_set"
dform false_set_df : except_mode[src] :: false_set = `"false_set"
dform val_true_df : except_mode[src] :: val_true = `"val_true"
dform val_false_df : except_mode[src] :: val_false = `"val_false"

(* Functions. *)
dform lambda_df1 : except_mode[src] :: lambda{ x. 'f } =
   `"(" Nuprl_font!lambda slot{'x} `"." slot{'f} `")"
dform lambda_df0 : except_mode[src] :: lambda{ 'f } =
   `"(" Nuprl_font!lambda `"()." slot{'f} `")"
dform apply_df : except_mode[src] :: apply{ 'f; 'x } =
   `"(" slot{'f} `" " slot{'x} `")"
dform fix_df : except_mode[src] :: fix{ f. 'b } =
   pushm[0] szone push_indent `"(fix " slot{'f} `"." hspace
   szone slot{'b} `")" ezone popm
   ezone popm

(* Misc. *)
dform unknownFun_df : except_mode[src] :: unknownFun = `"UnknownFun"

(*************************************************************************
 * Rewrites.
 * These are how we express FIR evaluation.
 *************************************************************************)

(*
 * Boolean type.
 *)

prim_rw reduce_true_set : true_set <--> int_set{ 1; 1 }
prim_rw reduce_false_set : false_set <--> int_set{ 0; 0 }
prim_rw reduce_val_true : val_true <--> 1
prim_rw reduce_val_false : val_false <--> 0

(*
 * Functions.
 *)

prim_rw reduce_beta : apply{ lambda{ x. 'f['x] }; 'y } <--> 'f['y]
prim_rw reduce_apply_nil : apply{ lambda{ 'f }; nil } <--> 'f
prim_rw reduce_fix : fix{ f. 'b['f] } <--> 'b[ fix{ f. 'b['f] } ]

(*
 * Types.
 *)

prim_rw reduce_tyVar : tyVar{ 'ty_var } <--> 'ty_var

(**************
 * Expressions.
 **************)

(* Identity (polymorphic). *)
prim_rw reduce_idOp : unop_exp{ idOp; 'a1 } <--> 'a1

(* Pointer equality. *)
prim_rw reduce_eqEqOp : binop_exp{ eqEqOp; 'a1; 'a2 } <-->
   ifthenelse{ beq_int{'a1; 'a2}; val_true; val_false }
prim_rw reduce_neqEqOp : binop_exp{ neqEqOp; 'a1; 'a2 } <-->
   ifthenelse{ beq_int{'a1; 'a2}; val_false; val_true }

(*
 * Normal values.
 * I could turn reduce_atomEnum into a conditional rewrite
 *    to make sure that 0 <= 'num < 'bound,
 *    but I don't see a compelling reason to do this as it
 *    just complicates evaluation.
 *)
prim_rw reduce_atomInt : atomInt{ 'num } <--> 'num
prim_rw reduce_atomEnum : atomEnum{ 'bound; 'num } <--> 'num
prim_rw reduce_atomRawInt : atomRawInt{ 'num } <--> 'num
prim_rw reduce_atomVar : atomVar{ 'var } <--> 'var

(* Primitive operations. *)
prim_rw reduce_letUnop :
   letUnop{ 'op; 'ty; 'a1; v. 'exp['v] } <-->
   'exp[ unop_exp{ 'op; 'a1 } ]
prim_rw reduce_letBinop :
   letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ binop_exp{ 'op; 'a1; 'a2 } ]

(*
 * Function application.
 * letExt is treated as a no-op, on the assumption that it
 * has a side-effect that we don't need to worry about here.
 * If that's not true... uh-oh.
 *)
prim_rw reduce_letExt :
   letExt{ 'ty; 'string; 'ty_of_str; 'atom_list; v. 'exp['v] } <-->
   'exp[it]

(*
 * Control.
 * If the case list is nil, we can't evaluate the match expression.
 *)
prim_rw reduce_match_int :
   "match"{ number[i:n]; cons{ matchCase{'set; 'e }; 'el } } <-->
   ifthenelse{ member{ number[i:n]; 'set };
      'e;
      ."match"{ number[i:n]; 'el } }

(* Allocation. *)
prim_rw reduce_allocTuple :
   letAlloc{ allocTuple{ 'ty; 'atom_list }; v. 'exp['v] } <-->
   'exp['atom_list]
prim_rw reduce_allocArray :
   letAlloc{ allocArray{ 'ty; 'atom_list }; v. 'exp['v] } <-->
   'exp['atom_list]

(*
 * Subscripting.
 * For evaluation purposes, 'subop is completely ignored.
 *)
prim_rw reduce_letSubscript :
   letSubscript{ 'subop; 'ty; 'var; 'index; v. 'exp['v] } <-->
   'exp[ nth{ 'var; 'index } ]
prim_rw reduce_setSubscript :
   setSubscript{ 'subop; 'ty; 'var; 'index; 'new_val; v. 'exp['v] } <-->
   'exp[ replace_nth{ 'var; 'index; 'new_val } ]

(****************
 * Naml integers.
 ****************)

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

let firEvalT i =
   rwh (repeatC (applyAllC [
      reduce_true_set;
      reduce_false_set;
      reduce_val_true;
      reduce_val_false;

      reduce_beta;
      reduce_apply_nil;
      reduce_fix;

      reduce_tyVar;

      reduce_idOp;
      reduce_eqEqOp;
      reduce_neqEqOp;
      reduce_atomInt;
      reduce_atomEnum;
      reduce_atomRawInt;
      reduce_atomVar;
      reduce_letUnop;
      reduce_letBinop;
      reduce_letExt;
      reduce_match_int;
      reduce_allocTuple;
      reduce_allocArray;
      reduce_letSubscript;
      reduce_setSubscript;

      reduce_uminusIntOp;
      reduce_plusIntOp;
      reduce_minusIntOp;
      reduce_mulIntOp;
      reduce_divIntOp;
      reduce_remIntOp;
      reduce_maxIntOp;
      reduce_minIntOp;
      reduce_eqIntOp;
      reduce_neqIntOp;
      reduce_ltIntOp;
      reduce_leIntOp;
      reduce_gtIntOp;
      reduce_geIntOp;
      reduce_cmpIntOp;
      reduceTopC
   ] )) i
