(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define how to evaluate the FIR.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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

include Mp_mc_fir_base
include Mp_mc_fir_ty
include Mp_mc_fir_exp
include Itt_int_base
include Itt_int_ext
include Itt_rfun

open Top_conversionals
open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Modular arithmetic for integers.
 *)

(* Precision of naml integers. *)

declare naml_prec

(* Computes base ^ exp where base and exp are integers, with exp non-neg. *)

declare pow{ 'base; 'exp }

(*
 * Converts num to an appropriate value for an integer of precision bytes,
 * signed or unsigned.
 *)

declare mod_arith{ 'int_precision; 'int_signed; 'num }
declare mod_arith_signed{ 'int_precision; 'num }
declare mod_arith_unsigned{ 'int_precision; 'num }


(*
 * Expressions.
 *)

declare unop_exp{ 'op; 'ty; 'a1 }
declare binop_exp{ 'op; 'ty; 'a1; 'a2 }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(*
 * Modular arithmetic for integers.
 *)

dform naml_prec_df : except_mode[src] :: naml_prec =
   `"naml_prec"
dform pow_df : except_mode[src] :: pow{ 'base; 'exp } =
   `"(" slot{'base}  Nuprl_font!sup{'exp} `")"
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

(*
 * Expressions.
 *)

dform unop_exp_df : except_mode[src] :: unop_exp{ 'op; 'ty; 'a1 } =
   slot{'op} `"(" slot{'a1} `"):" slot{'ty}
dform binop_exp_df : except_mode[src] :: binop_exp{ 'op; 'ty; 'a1; 'a2 } =
   `"(" slot{'a1} `" " slot{'op} `" " slot{'a2} `"):" slot{'ty}

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(*
 * Modular arithmetic for integers.
 *)

prim_rw reduce_naml_prec :
   naml_prec <--> 31
prim_rw reduce_int8 :
   int8 <--> 8
prim_rw reduce_int16 :
   int16 <--> 16
prim_rw reduce_int32 :
   int32 <--> 32
prim_rw reduce_int64 :
   int64 <--> 64

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
   pow{ 2; 63 } <--> 9223372036854775808
interactive_rw reduce_pow_2_64 :
   pow{ 2; 64 } <--> 18446744073709551616

prim_rw reduce_mod_arith1 :
   mod_arith{ 'int_precision; signedInt; 'num } <-->
   mod_arith_signed{ 'int_precision; 'num }
prim_rw reduce_mod_arith2 :
   mod_arith{ 'int_precision; unsignedInt; 'num } <-->
   mod_arith_unsigned{ 'int_precision; 'num }

prim_rw reduce_mod_arith_signed :
   mod_arith_signed{ 'int_precision; 'num } <-->
   (lambda{ x.
      ifthenelse{ ge_bool{'x; pow{2; ('int_precision -@ 1)}};
         ('x -@ pow{2; 'int_precision});
         'x
      }
    } ('num %@ pow{2; 'int_precision}) )

prim_rw reduce_mod_arith_unsigned :
   mod_arith_unsigned{ 'int_precision; 'num } <-->
   ( 'num %@ pow{2; 'int_precision} )

(*
 * Unary operations.
 *)

(* Identity (polymorphic). *)

prim_rw reduce_idOp :
   unop_exp{ idOp; 'ty; 'atom1 } <--> 'atom1

(* Naml ints. *)

prim_rw reduce_uminusIntOp :
   unop_exp{ uminusIntOp; tyInt; atomInt{'atom1} } <-->
   atomInt{ ."minus"{'atom1} }

(*
 * Binary operations.
 *)

(* Naml ints. *)

prim_rw reduce_plusIntOp :
   binop_exp{ plusIntOp; tyInt; atomInt{'atom1}; atomInt{'atom2} } <-->
   atomInt{ mod_arith{ naml_prec; signedInt; ('atom1 +@ 'atom2) } }
prim_rw reduce_minusIntOp :
   binop_exp{ minusIntOp; tyInt; atomInt{'atom1}; atomInt{'atom2} } <-->
   atomInt{ mod_arith{ naml_prec; signedInt; ('atom1 -@ 'atom2) } }
prim_rw reduce_mulIntOp :
   binop_exp{ mulIntOp; tyInt; atomInt{'atom1}; atomInt{'atom2} } <-->
   atomInt{ mod_arith{ naml_prec; signedInt; ('atom1 *@ 'atom2) } }
prim_rw reduce_divIntOp :
   binop_exp{ divIntOp; tyInt; atomInt{'atom1}; atomInt{'atom2} } <-->
   atomInt{ mod_arith{ naml_prec; signedInt; ('atom1 /@ 'atom2) } }
prim_rw reduce_remIntOp :
   binop_exp{ remIntOp; tyInt; atomInt{'atom1}; atomInt{'atom2} } <-->
   atomInt{ mod_arith{ naml_prec; signedInt; ('atom1 %@ 'atom2) } }
prim_rw reduce_maxIntOp :
   binop_exp{ maxIntOp; tyInt; atomInt{'atom1}; atomInt{'atom2} } <-->
   atomInt{ ifthenelse{ lt_bool{'atom1; 'atom2}; 'atom2; 'atom1 } }
prim_rw reduce_minIntOp :
   binop_exp{ minIntOp; tyInt; atomInt{'atom1}; atomInt{'atom2} } <-->
   atomInt{ ifthenelse{ lt_bool{'atom1; 'atom2}; 'atom1; 'atom2 } }

(* Native ints. *)

prim_rw reduce_plusRawIntOp :
   binop_exp{ plusRawIntOp{'p; 's}; tyRawInt{'p; 's};
              atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2} } <-->
   atomRawInt{ 'p; 's; mod_arith{ 'p; 's; ('a1 +@ 'a2) } }
prim_rw reduce_minusRawIntOp :
   binop_exp{ minusRawIntOp{'p; 's}; tyRawInt{'p; 's};
              atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2} } <-->
   atomRawInt{ 'p; 's; mod_arith{ 'p; 's; ('a1 -@ 'a2) } }
prim_rw reduce_mulRawIntOp :
   binop_exp{ mulRawIntOp{'p; 's}; tyRawInt{'p; 's};
              atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2} } <-->
   atomRawInt{ 'p; 's; mod_arith{ 'p; 's; ('a1 *@ 'a2) } }
prim_rw reduce_divRawIntOp :
   binop_exp{ divRawIntOp{'p; 's}; tyRawInt{'p; 's};
              atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2} } <-->
   atomRawInt{ 'p; 's; mod_arith{ 'p; 's; ('a1 /@ 'a2) } }
prim_rw reduce_remRawIntOp :
   binop_exp{ remRawIntOp{'p; 's}; tyRawInt{'p; 's};
              atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2} } <-->
   atomRawInt{ 'p; 's; mod_arith{ 'p; 's; ('a1 %@ 'a2) } }
prim_rw reduce_maxRawIntOp :
   binop_exp{ maxRawIntOp{'p; 's}; tyRawInt{'p; 's};
              atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2} } <-->
   atomRawInt{ 'p; 's; ifthenelse{ lt_bool{'a1; 'a2}; 'a2; 'a1 } }
prim_rw reduce_minRawIntOp :
   binop_exp{ minRawIntOp{'p; 's}; tyRawInt{'p; 's};
              atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2} } <-->
   atomRawInt{ 'p; 's; ifthenelse{ lt_bool{'a1; 'a2}; 'a1; 'a2 } }

(*
 * Normal values. *)

prim_rw reduce_atomVar_atomNil :
   atomVar{ atomNil{ 'ty } } <--> atomNil{ 'ty }
prim_rw reduce_atomVar_atomInt :
   atomVar{ atomInt{'int} } <--> atomInt{'int}
prim_rw reduce_atomVar_atomEnum :
   atomVar{ atomEnum{ 'int1; 'int2 } } <-->
   atomEnum{ 'int1; 'int2 }
prim_rw reduce_atomVar_atomRawInt :
   atomVar{ atomRawInt{ 'int_precision; 'int_signed; 'num } } <-->
   atomRawInt{ 'int_precision; 'int_signed; 'num }
prim_rw reduce_atomVar_atomFloat :
   atomVar{ atomFloat{ 'float_precision; 'num } } <-->
   atomFloat{ 'float_precision; 'num }
prim_rw reduce_atomVar_atomConst :
   atomVar{ atomConst{ 'ty; 'ty_var; 'int } } <-->
   atomConst{ 'ty; 'ty_var; 'int }

(*
 * Expressions.
 *)

(* Primitive operations. *)

prim_rw reduce_letUnop :
   letUnop{ 'ty; 'unop; 'atom; var. 'exp['var] } <-->
   'exp[ unop_exp{ 'unop; 'ty; 'atom } ]
prim_rw reduce_letBinop :
   letBinop{ 'ty; 'binop; 'atom1; 'atom2; var. 'exp['var] } <-->
   'exp[ binop_exp{ 'binop; 'ty; 'atom1; 'atom2 } ]

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
      reduce_mod_arith1;
      reduce_mod_arith2;
      reduce_mod_arith_signed;
      reduce_mod_arith_unsigned;

      reduce_plusIntOp;
      reduce_minusIntOp;
      reduce_mulIntOp;
      reduce_divIntOp;
      reduce_remIntOp;
      reduce_maxIntOp;
      reduce_minIntOp;

      reduce_plusRawIntOp;
      reduce_minusRawIntOp;
      reduce_mulRawIntOp;
      reduce_divRawIntOp;
      reduce_remRawIntOp;
      reduce_maxRawIntOp;
      reduce_minRawIntOp;

      reduce_atomVar_atomNil;
      reduce_atomVar_atomInt;
      reduce_atomVar_atomEnum;
      reduce_atomVar_atomRawInt;
      reduce_atomVar_atomFloat;
      reduce_atomVar_atomConst;

      reduce_letUnop;
      reduce_letBinop;

      reduceTopC (* reduce everything else; mainly for Itt term reductions. *)
   ] )) i
