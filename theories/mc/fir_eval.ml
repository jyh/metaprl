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

include Mc_set
include Fir_ty
include Fir_exp
include Itt_list2
include Itt_int_base
include Itt_int_ext

open Top_conversionals
open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Modular arithmetic for integers.
 *)

declare naml_prec
declare pow{ 'base; 'exp }
declare mod_arith{ 'precision; 'sign; 'num }
declare mod_arith_signed{ 'precision; 'num }
declare mod_arith_unsigned{ 'precision; 'num }

(*
 * Boolean type.
 *)

declare true_set
declare false_set
declare atomEnum_eq{ 'a; 'b }

(*
 * Functions.
 *)

declare lambda{ x. 'f['x] }
declare lambda{ 'f }
declare apply{ 'f; 'x }
declare fix{ f. 'b['f] }

(*
 * Expressions.
 *)

declare unop_exp{ 'op; 'ty; 'a1 }
declare binop_exp{ 'op; 'ty; 'a1; 'a2 }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Modular arithmetic for integers. *)

dform naml_prec_df : except_mode[src] :: naml_prec =
   `"naml_prec"
dform pow_df : except_mode[src] :: pow{ 'base; 'exp } =
   slot{'base}  Nuprl_font!sup{'exp}
dform mod_arith_df : except_mode[src] ::
   mod_arith{ 'precision; 'sign; 'num } =
   `"mod_arith(" slot{'precision} `", " slot{'sign}
   `", " slot{'num} `")"
dform mod_arith_signed_df : except_mode[src] ::
   mod_arith_signed{ 'precision; 'num } =
   `"mod_arith_signed(" slot{'precision} `", " slot{'num} `")"
dform _mod_arith_unsigned_df : except_mode[src] ::
   mod_arith_unsigned{ 'precision; 'num } =
   `"mod_arith_unsigned(" slot{'precision} `", " slot{'num} `")"

(* Boolean type *)

dform true_set_df : except_mode[src] :: true_set = `"true_set"
dform false_set_df : except_mode[src] :: false_set = `"false_set"
dform atomEnum_eq_df : except_mode[src] :: atomEnum_eq{ 'a; 'b } =
   `"AtomEnum_Eq(" slot{'a} `", " slot{'b} `")"

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

(* Expressions. *)

dform unop_exp_df : except_mode[src] :: unop_exp{ 'op; 'ty; 'a1 } =
   slot{'op} `"(" slot{'a1} `"):" slot{'ty}
dform binop_exp_df : except_mode[src] :: binop_exp{ 'op; 'ty; 'a1; 'a2 } =
   `"(" slot{'a1} `" " slot{'op} `" " slot{'a2} `"):" slot{'ty}

(*************************************************************************
 * Rewrites.
 * These are how we express FIR evaluation.
 *************************************************************************)

(*
 * Modular arithmetic for integers.
 *)

prim_rw reduce_naml_prec : naml_prec <--> 31
prim_rw reduce_int8 : int8 <--> 8
prim_rw reduce_int16 : int16 <--> 16
prim_rw reduce_int32 : int32 <--> 32
prim_rw reduce_int64 : int64 <--> 64

prim_rw reduce_pow :
   pow{ 'base; 'exp } <-->
   ind{ 'exp; i, j. 1; 1; i, j. ('base *@ 'j) }
interactive_rw reduce_pow_2_7 :
   pow{ 2; 7 } <--> 128
interactive_rw reduce_pow_2_8 :
   pow{ 2; 8 } <--> 256
interactive_rw reduce_pow_2_15 :
   pow{ 2; 15 } <--> 32768
interactive_rw reduce_pow_2_16 :
   pow{ 2; 16 } <--> 65536
interactive_rw reduce_pow_2_30 :
   pow{ 2; 30 } <--> 1073741824
interactive_rw reduce_pow_2_31 :
   pow{ 2; 31 } <--> 2147483648
interactive_rw reduce_pow_2_32 :
   pow{ 2; 32 } <--> 4294967296
interactive_rw reduce_pow_2_63 :
   pow{ 2; 63 } <-->  9223372036854775808
interactive_rw reduce_pow_2_64 :
   pow{ 2; 64 } <--> 18446744073709551616

prim_rw reduce_mod_arith :
   mod_arith{ 'precision; 'sign; 'num } <-->
   ifthenelse{ atomEnum_eq{'sign; val_true};
      mod_arith_signed{ 'precision; 'num };
      mod_arith_unsigned{ 'precision; 'num }}
prim_rw reduce_mod_arith_signed :
   mod_arith_signed{ 'precision; 'num } <-->
   (lambda{ x.
      ifthenelse{ ge_bool{'x; pow{2; ('precision -@ 1)}};
         ('x -@ pow{2; 'precision});
         'x
      }
    } ('num %@ pow{2; 'precision}) )
prim_rw reduce_mod_arith_unsigned :
   mod_arith_unsigned{ 'precision; 'num } <-->
   ( 'num %@ pow{2; 'precision} )

(*
 * Boolean type.
 *)

prim_rw reduce_true_set : true_set <--> int_set{ cons{interval{1;1}; nil} }
prim_rw reduce_false_set : false_set <--> int_set{ cons{interval{0;0}; nil} }
prim_rw reduce_val_true : val_true <--> atomEnum{ 2; 1 }
prim_rw reduce_val_false : val_false <--> atomEnum{ 2; 0 }
prim_rw reduce_atomEnum_eq_atom :
   atomEnum_eq{ atomEnum{'a; 'b}; atomEnum{'c; 'd} } <-->
   band{ beq_int{'a; 'c}; beq_int{'b; 'd} }
prim_rw reduce_atomEnum_eq_num :
   atomEnum_eq{ 'a; 'b } <-->
   beq_int{ 'a; 'b }


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

prim_rw reduce_idOp : unop_exp{ idOp; 'ty; 'a1 } <--> 'a1

(*
 * Normal values.
 * I could turn reduce_atomEnum into a conditional rewrite
 *    to make sure that 0 <= 'num < 'bound,
 *    but I don't see a compelling reason to do this as it
 *    just complicates evaluation.
 *)

prim_rw reduce_atomInt : atomInt{ 'num } <--> 'num
prim_rw reduce_atomEnum : atomEnum{ 'bound; 'num } <--> 'num
prim_rw reduce_atomRawInt : atomRawInt{ 'p; 's; 'num } <--> 'num
prim_rw reduce_atomVar : atomVar{ 'var } <--> 'var

(* Primitive operations. *)

prim_rw reduce_letUnop :
   letUnop{ 'op; 'ty; 'a1; v. 'exp['v] } <-->
   'exp[ unop_exp{ 'op; 'ty; 'a1 } ]
prim_rw reduce_letBinop :
   letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ binop_exp{ 'op; 'ty; 'a1; 'a2 } ]

(*
 * Function application.
 * letExt is treated as a no-op, on the assumption that it
 * has a side-effect that we don't need to worry about here.
 * If that's not true... uh-oh.
 *)

prim_rw reduce_letExt :
   letExt{ 'ty; 'string; 'ty_of_str; 'atom_list; v. 'exp['v] } <-->
   'exp[it]

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
   unop_exp{ uminusIntOp; tyInt; 'a1 } <-->
   "minus"{'a1}

(*
 * Standard binary arithmetic operators.
 * We rely on base_meta and friends to stop div and rem by zero.
 *)

prim_rw reduce_plusIntOp :
   binop_exp{ plusIntOp; tyInt; 'a1; 'a2 } <-->
   atomInt{ mod_arith{ naml_prec; val_true; ('a1 +@ 'a2) } }
prim_rw reduce_minusIntOp :
   binop_exp{ minusIntOp; tyInt; 'a1; 'a2 } <-->
   atomInt{ mod_arith{ naml_prec; val_true; ('a1 -@ 'a2) } }
prim_rw reduce_mulIntOp :
   binop_exp{ mulIntOp; tyInt; 'a1; 'a2 } <-->
   atomInt{ mod_arith{ naml_prec; val_true; ('a1 *@ 'a2) } }
prim_rw reduce_divIntOp :
   binop_exp{ divIntOp; tyInt; 'a1; 'a2 } <-->
   atomInt{ mod_arith{ naml_prec; val_true; ('a1 /@ 'a2) } }
prim_rw reduce_remIntOp :
   binop_exp{ remIntOp; tyInt; 'a1; 'a2 } <-->
   atomInt{ mod_arith{ naml_prec; val_true; ('a1 %@ 'a2) } }

(* Max / min. *)

prim_rw reduce_maxIntOp :
   binop_exp{ maxIntOp; tyInt; 'a1; 'a2 } <-->
   atomInt{ ifthenelse{ lt_bool{'a1; 'a2}; 'a2; 'a1 } }
prim_rw reduce_minIntOp :
   binop_exp{ minIntOp; tyInt; 'a1; 'a2 } <-->
   atomInt{ ifthenelse{ lt_bool{'a1; 'a2}; 'a1; 'a2 } }

(* Boolean comparisons. *)

prim_rw reduce_eqIntOp :
   binop_exp{ eqIntOp; tyEnum{ 2 }; 'a1; 'a2 } <-->
   ifthenelse{ beq_int{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_neqIntOp :
   binop_exp{ neqIntOp; tyEnum{ 2 }; 'a1; 'a2 } <-->
   ifthenelse{ bneq_int{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_ltIntOp :
   binop_exp{ ltIntOp; tyEnum{ 2 }; 'a1; 'a2 } <-->
   ifthenelse{ lt_bool{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_leIntOp :
   binop_exp{ leIntOp; tyEnum{ 2 }; 'a1; 'a2 } <-->
   ifthenelse{ le_bool{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_gtIntOp :
   binop_exp{ gtIntOp; tyEnum{ 2 }; 'a1; 'a2 } <-->
   ifthenelse{ gt_bool{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_geIntOp :
   binop_exp{ geIntOp; tyEnum{ 2 }; 'a1; 'a2 } <-->
   ifthenelse{ ge_bool{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_cmpIntOp :
   binop_exp{ cmpIntOp; tyInt; 'a1; 'a2 } <-->
   ifthenelse{ beq_int{'a1; 'a2};
      atomInt{ 0 };
      ifthenelse{ lt_bool{'a1; 'a2};
         atomInt{ (-1) };
         atomInt{ 1 }
      }
   }

(******************
 * Native integers.
 ******************)

(*
 * Here, I rely on the fact that MetaPRL will represent abitrarily
 * large integers natively.
 *)

(*
 * Standard binary arithmetic operators.
 * I rely on base_meta and friends to stop div and rem by zero.
 *)

prim_rw reduce_plusRawIntOp :
   binop_exp{ plusRawIntOp{'p; 's}; tyRawInt{'p; 's}; 'a1; 'a2 } <-->
   atomRawInt{ 'p; 's; mod_arith{ 'p; 's; ('a1 +@ 'a2) } }
prim_rw reduce_minusRawIntOp :
   binop_exp{ minusRawIntOp{'p; 's}; tyRawInt{'p; 's}; 'a1; 'a2 } <-->
   atomRawInt{ 'p; 's; mod_arith{ 'p; 's; ('a1 -@ 'a2) } }
prim_rw reduce_mulRawIntOp :
   binop_exp{ mulRawIntOp{'p; 's}; tyRawInt{'p; 's}; 'a1; 'a2 } <-->
   atomRawInt{ 'p; 's; mod_arith{ 'p; 's; ('a1 *@ 'a2) } }
prim_rw reduce_divRawIntOp :
   binop_exp{ divRawIntOp{'p; 's}; tyRawInt{'p; 's}; 'a1; 'a2 } <-->
   atomRawInt{ 'p; 's; mod_arith{ 'p; 's; ('a1 /@ 'a2) } }
prim_rw reduce_remRawIntOp :
   binop_exp{ remRawIntOp{'p; 's}; tyRawInt{'p; 's}; 'a1; 'a2 } <-->
   atomRawInt{ 'p; 's; mod_arith{ 'p; 's; ('a1 %@ 'a2) } }

(* Max / min. *)

prim_rw reduce_maxRawIntOp :
   binop_exp{ maxRawIntOp{'p; 's}; tyRawInt{'p; 's}; 'a1; 'a2 } <-->
   atomRawInt{ 'p; 's; ifthenelse{ lt_bool{'a1; 'a2}; 'a2; 'a1 } }
prim_rw reduce_minRawIntOp :
   binop_exp{ minRawIntOp{'p; 's}; tyRawInt{'p; 's}; 'a1; 'a2 } <-->
   atomRawInt{ 'p; 's; ifthenelse{ lt_bool{'a1; 'a2}; 'a1; 'a2 } }

(* Boolean comparisons. *)

prim_rw reduce_eqRawIntOp :
   binop_exp{ eqRawIntOp{'p; 's}; tyEnum{ 2 }; 'a1; 'a2 } <-->
   ifthenelse{ beq_int{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_neqRawIntOp :
   binop_exp{ neqRawIntOp{'p; 's}; tyEnum{ 2 }; 'a1; 'a2 } <-->
   ifthenelse{ bneq_int{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_ltRawIntOp :
   binop_exp{ ltRawIntOp{'p; 's}; tyEnum{ 2 }; 'a1; 'a2 } <-->
   ifthenelse{ lt_bool{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_leRawIntOp :
   binop_exp{ leRawIntOp{'p; 's}; tyEnum{ 2 }; 'a1; 'a2 } <-->
   ifthenelse{ le_bool{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_gtRawIntOp :
   binop_exp{ gtRawIntOp{'p; 's}; tyEnum{ 2 }; 'a1; 'a2 } <-->
   ifthenelse{ gt_bool{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_geRawIntOp :
   binop_exp{ geRawIntOp{'p; 's}; tyEnum{ 2 }; 'a1; 'a2 } <-->
   ifthenelse{ ge_bool{ 'a1; 'a2 }; val_true; val_false }
prim_rw reduce_cmpRawIntOp :
   binop_exp{ cmpRawIntOp{'p; 's}; tyRawInt{ int32; val_true }; 'a1; 'a2 } <-->
   ifthenelse{ beq_int{'a1; 'a2};
      atomRawInt{ int32; val_true; 0 };
      ifthenelse{ lt_bool{'a1; 'a2};
         atomRawInt{ int32; val_true; (-1) };
         atomRawInt{ int32; val_true; 1 }
      }
   }

(*************************************************************************
 * Automation.
 *************************************************************************)

let firEvalT i =
   rwh (repeatC (applyAllC [
      reduce_naml_prec;
      reduce_int8;
      reduce_int16;
      reduce_int32;
      reduce_int64;


      reduce_pow_2_7;
      reduce_pow_2_8;
      reduce_pow_2_15;
      reduce_pow_2_16;
      reduce_pow_2_30;
      reduce_pow_2_31;
      reduce_pow_2_32;
      reduce_pow_2_63;
      reduce_pow_2_64;
      reduce_pow;

      reduce_mod_arith;
      reduce_mod_arith_signed;
      reduce_mod_arith_unsigned;

      reduce_true_set;
      reduce_false_set;
      reduce_val_true;
      reduce_val_false;
      reduce_atomEnum_eq_atom;
      reduce_atomEnum_eq_num;

      reduce_beta;
      reduce_apply_nil;
      reduce_fix;

      reduce_tyVar;

      reduce_idOp;
      reduce_atomInt;
      reduce_atomEnum;
      reduce_atomRawInt;
      reduce_atomVar;
      reduce_letUnop;
      reduce_letBinop;
      reduce_letExt;
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

      reduce_plusRawIntOp;
      reduce_minusRawIntOp;
      reduce_mulRawIntOp;
      reduce_divRawIntOp;
      reduce_remRawIntOp;
      reduce_maxRawIntOp;
      reduce_minRawIntOp;
      reduce_eqRawIntOp;
      reduce_neqRawIntOp;
      reduce_ltRawIntOp;
      reduce_leRawIntOp;
      reduce_gtRawIntOp;
      reduce_geRawIntOp;
      reduce_cmpRawIntOp;

      reduceTopC
   ] )) i
