doc <:doc< 
   @begin[doc]
   @module[Mp_mc_fir_eval]
  
   The @tt[Mp_mc_fir_eval] module defines the operational semantics
   of the FIR.
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.
  
   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.
  
   Copyright (C) 2002 Brian Emre Aydemir, Caltech
  
   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.
  
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
  
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
  
   Author: Brian Emre Aydemir
   @email{emre@its.caltech.edu}
   @end[license]
>>

doc <:doc< @doc{docoff} >>
extends Itt_bool
extends Itt_int_base
extends Itt_int_ext
extends Itt_list
extends Mp_mc_fir_base
extends Mp_mc_fir_ty
extends Mp_mc_fir_exp
doc docoff

open Top_conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Modular arithmetic for integers.
 *)

(* Precision of naml integers. Corresponds to tyInt. *)

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
 * Booleans, as represented in the FIR.
 *)

declare fir_true
declare fir_false

(*
 * Set (and interval) membership.
 *)

declare member{ 'value; 'set }

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
dform mod_arith_unsigned_df : except_mode[src] ::
   mod_arith_unsigned{ 'precision; 'num } =
   `"mod_arith_unsigned(" slot{'precision} `", " slot{'num} `")"

(*
 * Booleans, as represented in the FIR.
 *)

dform fir_true_df : except_mode[src] ::
   fir_true =
   `"Fir_true"
dform fir_false_df : except_mode[src] ::
   fir_false =
   `"Fir_false"

(*
 * Set (and interval) membership.
 *)

dform member_df : except_mode[src] ::
   member{ 'value; 'set } =
   `"member(" slot{'value} `"," slot{'set} `")"

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
 * Arithmetic in the FIR is not infinite precision.
 *)

(* Precompute some common powers of 2. *)

prim_rw reduce_pow :
   pow{ 'base; 'exp } <-->
   ifthenelse{ beq_int{'exp; 0}; 1; ('base *@ pow{'base; ('exp -@ 1)}) }

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

(* Perform 2's complement arithmetic in the precision specified. *)

prim_rw reduce_arith_signed_int8 :
   mod_arith{ int8; signedInt; 'num } <-->
   mod_arith_signed{ 8; 'num }

prim_rw reduce_arith_signed_int16 :
   mod_arith{ int16; signedInt; 'num } <-->
   mod_arith_signed{ 16; 'num }

prim_rw reduce_arith_signed_int32 :
   mod_arith{ int32; signedInt; 'num } <-->
   mod_arith_signed{ 32; 'num }

prim_rw reduce_arith_signed_int64 :
   mod_arith{ int64; signedInt; 'num } <-->
   mod_arith_signed{ 64; 'num }

prim_rw reduce_arith_signed_naml :
   mod_arith{ naml_prec; signedInt; 'num } <-->
   mod_arith_signed{ 31; 'num }

prim_rw reduce_arith_unsigned_int8 :
   mod_arith{ int8; unsignedInt; 'num } <-->
   mod_arith_unsigned{ 8; 'num }

prim_rw reduce_arith_unsigned_int16 :
   mod_arith{ int16; unsignedInt; 'num } <-->
   mod_arith_unsigned{ 16; 'num }

prim_rw reduce_arith_unsigned_int32 :
   mod_arith{ int32; unsignedInt; 'num } <-->
   mod_arith_unsigned{ 32; 'num }

prim_rw reduce_arith_unsigned_int64 :
   mod_arith{ int64; unsignedInt; 'num } <-->
   mod_arith_unsigned{ 64; 'num }

(* These perform the actual arithmetic. *)

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
 * Booleans, as represented in the FIR.
 *)

prim_rw reduce_fir_true :
   fir_true <-->
   atomEnum{ 2; 1 }

prim_rw reduce_fir_false :
   fir_false <-->
   atomEnum{ 2; 0 }

(*
 * Set (and interval) membership.
 *)

prim_rw reduce_member_interval :
   member{ 'value; interval{ 'left; 'right } } <-->
   band{ le_bool{'left; 'value}; le_bool{'value; 'right} }

prim_rw reduce_member_int_set :
   member{ 'value; int_set{ cons{'interval; 'tail} } } <-->
   bor{ member{'value; 'interval}; member{'value; int_set{'tail}} }

prim_rw reduce_member_rawint_set :
   member{ 'value; rawint_set{ 'p; 's; cons{'interval; 'tail} } } <-->
   bor{ member{'value; 'interval};
        member{'value; rawint_set{ 'p; 's; 'tail }} }

prim_rw reduce_member_int_set_empty :
   member{ 'value; int_set{ nil } } <-->
   bfalse

prim_rw reduce_member_rawint_set_empty :
   member{ 'value; rawint_set{ 'int_precision; 'int_signed; nil } } <-->
   bfalse

(*
 * Normal values.
 *)

(* We reduce atomVar wrappers that are no longer needed and
 * in fact constitute malformed FIR terms. We should never get
 * atomVar{ atomVar{ 'v } }, so there's no rewrite for this case.
 * The others occur when we substitute for bound variables. *)

prim_rw reduce_atomVar_atomNil :
   atomVar{ atomNil{ 'ty } } <-->
   atomNil{ 'ty }

prim_rw reduce_atomVar_atomInt :
   atomVar{ atomInt{ 'int } } <-->
   atomInt{ 'int }

prim_rw reduce_atomVar_atomEnum :
   atomVar{ atomEnum{ 'bound; 'value } } <-->
   atomEnum{ 'bound; 'value }

prim_rw reduce_atomVar_atomRawInt :
   atomVar{ atomRawInt{ 'int_precision; 'int_signed; 'num } } <-->
   atomRawInt{ 'int_precision; 'int_signed; 'num }

prim_rw reduce_atomVar_atomFloat :
   atomVar{ atomFloat{ 'float_precision; 'num } } <-->
   atomFloat{ 'float_precision; 'num }

prim_rw reduce_atomVar_atomLabel :
   atomVar{ atomLabel{ 'frame_label; 'atom_rawint } } <-->
   atomLabel{ 'frame_label; 'atom_rawint }

prim_rw reduce_atomVar_atomSizeof :
   atomVar{ atomSizeof{ 'var_list; 'atom_rawint } } <-->
   atomSizeof{ 'var_list; 'atom_rawint }

prim_rw reduce_atomVar_atomConst :
   atomVar{ atomConst{ 'ty; 'ty_var; 'int } } <-->
   atomConst{ 'ty; 'ty_var; 'int }

prim_rw reduce_atomVar_atomVar :
   atomVar{ atomVar{ 'v } } <-->
   atomVar{ 'v }

(*
 * Unary operations.
 *)

(* Note: I should have cases for each atom, so that I don't rely
 * on the order in which rewrites are applied. *)

prim_rw reduce_idOp_atomInt :
   letUnop{ tyInt; idOp; atomInt{ 'num }; var. 'exp['var] } <-->
   'exp[ atomInt{ 'num } ]

prim_rw reduce_idOp_atomEnum :
   letUnop{ tyEnum{'bound}; idOp; atomEnum{'bound; 'value}; v. 'exp['v] } <-->
   'exp[ atomEnum{'bound; 'value} ]

prim_rw reduce_idOp_atomRawInt :
   letUnop{ tyRawInt{'p; 's}; idOp; atomRawInt{'p; 's; 'n}; v. 'exp['v] } <-->
   'exp[ atomRawInt{'p; 's; 'n} ]

prim_rw reduce_idOp_atomFloat :
   letUnop{ tyFloat{'p}; idOp; atomFloat{'p; 'num}; var. 'exp['var] } <-->
   'exp[ atomFloat{ 'p; 'num } ]

(* Remove the atomVar wrapper since 'exp should already have that. *)
prim_rw reduce_idOp_atomVar :
   letUnop{ 'ty; idOp; atomVar{ 'symbol }; var. 'exp['var] } <-->
   'exp[ 'symbol ]

(*
 * Binary operations.
 *)

(* Naml integers. *)

prim_rw reduce_plusIntOp :
   letBinop{ tyInt; plusIntOp; atomInt{'a1}; atomInt{'a2}; v. 'exp['v] } <-->
   'exp[ atomInt{ mod_arith{ naml_prec; signedInt; ('a1 +@ 'a2) } } ]

prim_rw reduce_minusIntOp :
   letBinop{ tyInt; minusIntOp; atomInt{'a1}; atomInt{'a2}; v. 'exp['v] } <-->
   'exp[ atomInt{ mod_arith{ naml_prec; signedInt; ('a1 -@ 'a2) } } ]

prim_rw reduce_mulIntOp :
   letBinop{ tyInt; mulIntOp; atomInt{'a1}; atomInt{'a2}; v. 'exp['v] } <-->
   'exp[ atomInt{ mod_arith{ naml_prec; signedInt; ('a1 *@ 'a2) } } ]

prim_rw reduce_eqIntOp :
   letBinop{ tyEnum{2}; eqIntOp; atomInt{'a1}; atomInt{'a2}; v. 'exp['v] } <-->
   'exp[ ifthenelse{ beq_int{'a1;'a2}; fir_true; fir_false } ]

(* Native ints. *)

prim_rw reduce_plusRawIntOp :
   letBinop{ tyRawInt{'p;'s}; plusRawIntOp{'p;'s};
             atomRawInt{'p;'s;'a1}; atomRawInt{'p;'s;'a2}; v. 'exp['v] } <-->
   'exp[ atomRawInt{'p; 's; mod_arith{ 'p; 's; ('a1 +@ 'a2) } } ]

prim_rw reduce_minusRawIntOp :
   letBinop{ tyRawInt{'p;'s}; minusRawIntOp{'p;'s};
             atomRawInt{'p;'s;'a1}; atomRawInt{'p;'s;'a2}; v. 'exp['v] } <-->
   'exp[ atomRawInt{'p; 's; mod_arith{ 'p; 's; ('a1 -@ 'a2) } } ]

prim_rw reduce_mulRawIntOp :
   letBinop{ tyRawInt{'p;'s}; mulRawIntOp{'p;'s};
             atomRawInt{'p;'s;'a1}; atomRawInt{'p;'s;'a2}; v. 'exp['v] } <-->
   'exp[ atomRawInt{'p; 's; mod_arith{ 'p; 's; ('a1 *@ 'a2) } } ]

prim_rw reduce_eqRawIntOp :
   letBinop{ tyEnum{2}; eqRawIntOp{'p;'s};
             atomRawInt{'p;'s;'a1}; atomRawInt{'p;'s;'a2}; v. 'exp['v] } <-->
   'exp[ ifthenelse{ beq_int{'a1;'a2}; fir_true; fir_false } ]

(* Pointers. *)

prim_rw reduce_eqEqOp :
   letBinop{ tyEnum{2}; eqEqOp; atomInt{'a1}; atomInt{'a2}; v. 'exp['v] } <-->
   'exp[ ifthenelse{ beq_int{'a1;'a2}; fir_true; fir_false } ]

(*
 * Control.
 *)

prim_rw reduce_matchExp_atomEnum :
   matchExp{ atomEnum{'bound; 'value}; 'cases } <-->
   matchExp{ 'value; 'cases }

prim_rw reduce_matchExp_atomInt :
   matchExp{ atomInt{ 'num }; 'cases } <-->
   matchExp{ 'num; 'cases }

prim_rw reduce_matchExp_number :
   matchExp{ number[i:n]; cons{matchCase{'label; 'set; 'exp}; 'tail} } <-->
   ifthenelse{ member{number[i:n]; 'set};
               'exp;
               matchExp{ number[i:n]; 'tail } }

(*************************************************************************
 * Automation
 *************************************************************************)

let firExpEvalC =
   repeatC (higherC (applyAllC [

      reduce_pow;
      reduce_pow_2_7;
      reduce_pow_2_8;
      reduce_pow_2_15;
      reduce_pow_2_16;
      reduce_pow_2_30;
      reduce_pow_2_31;
      reduce_pow_2_32;
      reduce_pow_2_63;
      reduce_pow_2_64;

      reduce_arith_signed_int8;
      reduce_arith_signed_int16;
      reduce_arith_signed_int32;
      reduce_arith_signed_int64;
      reduce_arith_signed_naml;
      reduce_arith_unsigned_int8;
      reduce_arith_unsigned_int16;
      reduce_arith_unsigned_int32;
      reduce_arith_unsigned_int64;

      reduce_mod_arith_signed;
      reduce_mod_arith_unsigned;

      reduce_fir_true;
      reduce_fir_false;

      reduce_member_interval;
      reduce_member_int_set;
      reduce_member_rawint_set;
      reduce_member_int_set_empty;
      reduce_member_rawint_set_empty;

      reduce_atomVar_atomNil;
      reduce_atomVar_atomInt;
      reduce_atomVar_atomEnum;
      reduce_atomVar_atomRawInt;
      reduce_atomVar_atomFloat;
      reduce_atomVar_atomLabel;
      reduce_atomVar_atomSizeof;
      reduce_atomVar_atomConst;
      reduce_atomVar_atomVar;

      reduce_idOp_atomInt;
      reduce_idOp_atomEnum;
      reduce_idOp_atomRawInt;
      reduce_idOp_atomFloat;
      reduce_idOp_atomVar;

      reduce_plusIntOp;
      reduce_minusIntOp;
      reduce_mulIntOp;
      reduce_eqIntOp;

      reduce_plusRawIntOp;
      reduce_minusRawIntOp;
      reduce_mulRawIntOp;
      reduce_eqRawIntOp;

      reduce_eqEqOp;

      reduce_matchExp_atomEnum;
      reduce_matchExp_atomInt;
      reduce_matchExp_number;

      reduceTopC

   ] ))
