(*!
 * @begin[doc]
 * @theory[Mp_mc_fir_exp]
 *
 * The @tt{Mp_mc_fir_exp} module defines terms to represent
 * FIR expressions.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
 * @email{emre@its.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Base_theory
(*! @docoff *)

open Mp_mc_term_op
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*!
 * @begin[doc]
 * @terms
 * @thysubsection{Unary operations}
 *
 * These are the unary operations in the FIR.  They are used in
 * @hrefterm[letUnop] as the @tt{unop} subterm.  Each of the operators
 * here can only be applied to values of a given type.  In instances
 * where the type has precision and / or signing subterms
 * (such as @hrefterm[tyRawInt]), the qualifiers in the operator
 * must also match those of the type in order for the @hrefterm[letUnop]
 * term to be well-formed.
 *
 * @tt{idOp} is a polymorphic identity operator.
 * @end[doc]
 *)

declare idOp

(*!
 * @begin[doc]
 *
 * @tt{uminusIntOp} is unary arithmetic negation and @tt{notIntOp}
 * is bitwise negation.  They operate of values of type @hrefterm[tyInt].
 * @end[doc]
 *)

declare uminusIntOp
declare notIntOp

(*!
 * @begin[doc]
 *
 * Bit fields.
 * @end[doc]
 *)

declare rawBitFieldOp{ 'int_precision; 'int_signed; 'int1; 'int2 }

(*!
 * @begin[doc]
 *
 * @tt{uminusRawIntOp} and @tt{notRawIntOp} are analogous to
 * @hrefterm[uminusIntOp] and @hrefterm[notIntOp], except they
 * operate on values of type @hrefterm[tyRawInt].
 * @end[doc]
 *)

declare uminusRawIntOp{ 'int_precision; 'int_signed }
declare notRawIntOp{ 'int_precision; 'int_signed }

(* Floats. *)

declare uminusFloatOp{ 'float_precision }
declare absFloatOp{ 'float_precision }
declare sinOp{ 'float_precision }
declare cosOp{ 'float_precision }
declare sqrtOp{ 'float_precision }

(* Coerce to int. *)

declare intOfFloatOp{ 'float_precision }

(* Coerce to float. *)

declare floatOfIntOp{ 'float_precision }
declare floatOfFloatOp{ 'float_precision1; 'float_precision2 }
declare floatOfRawIntOp{ 'float_precision; 'int_precision; 'int_signed }

(* Coerce to rawint. *)

declare rawIntOfIntOp{ 'int_precision; 'int_signed }
declare rawIntOfEnumOp{ 'int_precision; 'int_signed; 'int }
declare rawIntOfFloatOp{ 'int_precision; 'int_signed; 'float_precision }
declare rawIntOfRawIntOp{ 'dest_int_precision; 'dest_int_signed;
                          'src_int_precision;  'src_int_signed }

(* Integer/pointer coercions. *)

declare rawIntOfPointerOp{ 'int_precision; 'int_signed }
declare pointerOfRawIntOp{ 'int_precision; 'int_signed }

(* Pointer from a block pointer. *)

declare pointerOfBlockOp{ 'sub_block }

(*!
 * @begin[doc]
 * @thysubsection{Binary operations}
 *
 * These are the binary operations in the FIR.  They are used in
 * @hrefterm[letBinop] as the @tt{binop} subterm.  Each of the operators
 * here can only be applied to values of a given type.  In instances
 * where the type has precision and / or signing subterms
 * (such as @hrefterm[tyRawInt]), the qualifiers in the operator
 * must also match those of the type in order for the @hrefterm[letBinop]
 * term to be well-formed.
 *
 * @end[doc]
 *)

(* Enums. *)

declare andEnumOp{ 'int }
declare orEnumOp{ 'int }
declare xorEnumOp{ 'int }

(* Naml ints. *)

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
declare maxIntOp
declare minIntOp

declare eqIntOp
declare neqIntOp
declare ltIntOp
declare leIntOp
declare gtIntOp
declare geIntOp
declare cmpIntOp

(* Native ints. *)

declare plusRawIntOp{ 'int_precision; 'int_signed }
declare minusRawIntOp{ 'int_precision; 'int_signed }
declare mulRawIntOp{ 'int_precision; 'int_signed }
declare divRawIntOp{ 'int_precision; 'int_signed }
declare remRawIntOp{ 'int_precision; 'int_signed }
declare slRawIntOp{ 'int_precision; 'int_signed }
declare srRawIntOp{ 'int_precision; 'int_signed }
declare andRawIntOp{ 'int_precision; 'int_signed }
declare orRawIntOp{ 'int_precision; 'int_signed }
declare xorRawIntOp{ 'int_precision; 'int_signed }
declare maxRawIntOp{ 'int_precision; 'int_signed }
declare minRawIntOp{ 'int_precision; 'int_signed }

declare rawSetBitFieldOp{ 'int_precision; 'int_signed; 'int1; 'int2 }

declare eqRawIntOp{ 'int_precision; 'int_signed }
declare neqRawIntOp{ 'int_precision; 'int_signed }
declare ltRawIntOp{ 'int_precision; 'int_signed }
declare leRawIntOp{ 'int_precision; 'int_signed }
declare gtRawIntOp{ 'int_precision; 'int_signed }
declare geRawIntOp{ 'int_precision; 'int_signed }
declare cmpRawIntOp{ 'int_precision; 'int_signed }

(* Floats. *)

declare plusFloatOp{ 'float_precision }
declare minusFloatOp{ 'float_precision }
declare mulFloatOp{ 'float_precision }
declare divFloatOp{ 'float_precision }
declare remFloatOp{ 'float_precision }
declare maxFloatOp{ 'float_precision }
declare minFloatOp{ 'float_precision }

declare eqFloatOp{ 'float_precision }
declare neqFloatOp{ 'float_precision }
declare ltFloatOp{ 'float_precision }
declare leFloatOp{ 'float_precision }
declare gtFloatOp{ 'float_precision }
declare geFloatOp{ 'float_precision }
declare cmpFloatOp{ 'float_precision }

declare atan2Op{ 'float_precision }

(* Pointer equality. *)

declare eqEqOp
declare neqEqOp

(* Pointer arithmetic. *)

declare plusPointerOp{ 'sub_block; 'int_precision; 'int_signed }

(*!
 * @begin[doc]
 * @thysubsection{Fields (frame labels)}
 *
 * @end[doc]
 *)

declare frameLabel{ 'label1; 'label2; 'label3 }

(*!
 * @begin[doc]
 * @thysubsection{Normal values}
 *
 * @end[doc]
 *)

declare atomNil{ 'ty }
declare atomInt{ 'int }
declare atomEnum{ 'int1; 'int2 } (* 'int1 = bound, 'int2 = value *)
declare atomRawInt{ 'int_precision; 'int_signed; 'num }
declare atomFloat{ 'float_precision; 'num }
declare atomLabel{ 'frame_label; 'atom_rawint }
declare atomSizeof{ 'var_list; 'atom_rawint }
declare atomConst{ 'ty; 'ty_var; 'int }
declare atomVar{ 'var }

(*!
 * @begin[doc]
 * @thysubsection{Allocation operators}
 *
 * @end[doc]
 *)

declare allocTuple{ 'tuple_class; 'ty; 'atom_list }
declare allocUnion{ 'ty; 'ty_var; 'int; 'atom_list }
declare allocArray{ 'ty; 'atom_list }
declare allocVArray{ 'ty; 'sub_index; 'atom1; 'atom2 }
declare allocMalloc{ 'ty; 'atom }
declare allocFrame{ 'var }

(*!
 * @begin[doc]
 * @thysubsection{Tail calls / operations}
 *
 * @end[doc]
 *)

declare tailSysMigrate{ 'int; 'atom1; 'atom2; 'var; 'atom_list }
declare tailAtomic{ 'var; 'atom; 'atom_list }
declare tailAtomicRollback{ 'atom }
declare tailAtomicCommit{ 'var; 'atom_list }

(*!
 * @begin[doc]
 * @thysubsection{Predicates and assertions}
 *
 * These terms encode the safety checks that an FIR program must
 * perform in order to ensure that programs execute safely.
 * @end[doc]
 *)

declare isMutable{ 'var }
declare reserve{ 'atom1; 'atom2 }
declare boundsCheck{ 'subop; 'var; 'atom1; 'atom2 }
declare elementCheck{ 'ty; 'subop; 'var; 'atom }

(*!
 * @begin[doc]
 * @thysubsection{Debugging info}
 *
 * These terms are used to encode debugging information.
 * @end[doc]
 *)

declare debugLine{ 'string; 'int }
declare debugVarItem{ 'var1; 'ty; 'var2 }
declare debugVars{ 'debugVarItem_list }
declare debugString{ 'string }
declare debugContext{ 'debug_line; 'debug_vars }

(*!
 * @begin[doc]
 * @thysubsection{Expressions}
 *
 * @end[doc]
 *)

(* Primitive operations. *)

declare letUnop{ 'ty; 'unop; 'atom; var. 'exp['var] }
declare letBinop{ 'ty; 'binop; 'atom1; 'atom2; var. 'exp['var] }

(* Function application. *)

declare letExt{ 'ty1; 'string; 'ty2; 'atom_list; var. 'exp['var] }
declare tailCall{ 'label; 'var; 'atom_list }
declare specialCall{ 'label; 'tailop }

(* Control. *)

declare matchCase{ 'label; 'set; 'exp }
declare matchExp{ 'atom; 'matchCase_list }
declare typeCase{ 'atom1; 'atom2; 'var1; 'var2; 'exp1; 'exp2 }

(* Allocation. *)

declare letAlloc{ 'alloc_op; var. 'exp['var] }

(* Subscripting. *)

declare letSubscript{ 'subop; 'ty; 'var2; 'atom; var1. 'exp['var1] }
declare setSubscript{ 'subop; 'label; 'var; 'atom1; 'ty; 'atom2; 'exp }
declare setGlobal{ 'sub_value; 'label; 'var; 'ty; 'atom; 'exp }
declare memcpy{ 'subop; 'label; 'var1; 'atom1; 'var2; 'atom2; 'atom3; 'exp }

(* Assertions. *)

declare call{ 'label; 'var; 'atom_option_list; 'exp }
declare assertExp{ 'label; 'pred; 'exp }

(* Debugging. *)

declare debug{ 'debug_info; 'exp }

(*!
 * @begin[doc]
 * @thysubsection{Function definition}
 *
 * @end[doc]
 *)

declare fundef{ 'debug_line; 'ty; 'var_list; 'exp }

(*! @docoff *)

(*************************************************************************
 * Display forms.
 *************************************************************************)

(*
 * Unary operations.
 *)

(* Identity (polymorphic). *)

dform idOp_df : except_mode[src] ::
   idOp =
   `"idOp"

(* Naml ints. *)

dform uminusIntOp_df : except_mode[src] ::
   uminusIntOp =
   `"-"
dform notIntOp_df : except_mode[src] ::
   notIntOp =
   `"~"

(* Bit fields. *)

dform rawBitFieldOp_df : except_mode[src] ::
   rawBitFieldOp{ 'int_precision; 'int_signed; 'int1; 'int2 } =
   `"RawBitFieldOp(" slot{'int_precision} `"," slot{'int_signed} `","
   slot{'int1} `"," slot{'int2} `")"

(* Native ints. *)

dform uminusRawIntOp_df : except_mode[src] ::
   uminusRawIntOp{ 'int_precision; 'int_signed } =
   `"(-," slot{'int_precision} `"," slot{'int_signed } `")"
dform notRawIntOp_df : except_mode[src] ::
   notRawIntOp{ 'int_precision; 'int_signed } =
   `"(~," slot{'int_precision} `"," slot{'int_signed} `")"

(* Floats. *)

dform uminusFloatOp_df : except_mode[src] ::
   uminusFloatOp{ 'float_precision } =
   `"(-," slot{'float_precision} `")"
dform absFloatOp_df : except_mode[src] ::
   absFloatOp{ 'float_precision } =
   `"(abs," slot{'float_precision} `")"
dform sinOp_df : except_mode[src] ::
   sinOp{ 'float_precision } =
   `"(sin," slot{'float_precision} `")"
dform cosOp_df : except_mode[src] ::
   cosOp{ 'float_precision } =
   `"(cos," slot{'float_precision} `")"
dform sqrtOp_df : except_mode[src] ::
   sqrtOp{ 'float_precision } =
   `"(sqrt," slot{'float_precision} `")"

(* Coerce to int. *)

dform intOfFloatOp_df : except_mode[src] ::
   intOfFloatOp{ 'float_precision } =
   `"IntOfFloatOp(" slot{'float_precision} `")"

(* Coerce to float. *)

dform floatOfIntOp_df : except_mode[src] ::
   floatOfIntOp{ 'float_precision } =
   `"FloatOfIntOp(" slot{'float_precision} `")"
dform floatOfFLoatOp_df : except_mode[src] ::
   floatOfFloatOp{ 'float_precision1; 'float_precision2 } =
   `"FloatOfFloatOp(" slot{'float_precision1} `"," slot{'float_precision2} `")"
dform floatOfRawIntOp_df : except_mode[src] ::
   floatOfRawIntOp{ 'float_precision; 'int_precision; 'int_signed } =
   `"FloatOfRawIntOp(" slot{'float_precision} `"," slot{'int_precision}
   `"," slot{'int_signed} `")"

(* Coerce to rawint. *)

dform rawIntOfIntOp_df : except_mode[src] ::
   rawIntOfIntOp{ 'int_precision; 'int_signed } =
   `"RawIntOfInt(" slot{'int_precision} `"," slot{'int_signed} `")"
dform rawIntOfEnumOp_df : except_mode[src] ::
   rawIntOfEnumOp{ 'int_precision; 'int_signed; 'int } =
   `"RawIntOfEnumOp(" slot{'int_precision} `","
   slot{'int_signed} `"," slot{'int} `")"
dform rawIntOfFloatOp_df : except_mode[src] ::
   rawIntOfFloatOp{ 'int_precision; 'int_signed; 'float_precision } =
   `"RawIntOfFloatOp(" slot{'int_precision} `"," slot{'int_signed}
   `"," slot{'float_precision} `")"
dform rawIntOfRawIntOp_df : except_mode[src] ::
   rawIntOfRawIntOp{ 'dest_int_precision; 'dest_int_signed;
                     'src_int_precision; 'src_int_signed } =
   `"RawIntOfRawIntOp(" slot{'dest_int_precision} `"," slot{'dest_int_signed}
   `"," slot{'src_int_precision} `"," slot{'src_int_signed} `")"

(* Integer/pointer coercions. *)

dform rawIntOfPointerOp_df : except_mode[src] ::
   rawIntOfPointerOp{ 'int_precision; 'int_signed } =
   `"RawIntOfPointerOp(" slot{'int_precision} `"," slot{'int_signed} `")"
dform pointerOfRawIntOp_df : except_mode[src] ::
   pointerOfRawIntOp{ 'int_precision; 'int_signed } =
   `"PointerOfRawIntOp(" slot{'int_precision} `"," slot{'int_signed} `")"

(* Pointer from a block pointer. *)

dform pointerOfBlockOp_df : except_mode[src] ::
   pointerOfBlockOp{ 'sub_block } =
   `"PointerOfBlockOp(" slot{'sub_block} `")"

(*
 * Binary operations.
 *)

(* Enums. *)

dform andEnumOp_df : except_mode[src] ::
   andEnumOp{ 'int } =
   lzone `"AndEnumOp(" slot{'int} `")" ezone
dform orEnumOp_df : except_mode[src] ::
   orEnumOp{ 'int } =
   lzone `"OrEnumOp(" slot{'int} `")" ezone
dform xorEnumOp_df : except_mode[src] ::
   xorEnumOp{ 'int } =
   lzone `"XorEnumOp(" slot{'int} `")" ezone

(* Naml ints. *)

dform plusIntOp_df : except_mode[src] ::
   plusIntOp =
   `"+"
dform minusIntOp_df : except_mode[src] ::
   minusIntOp =
   `"-"
dform mulIntOp_df : except_mode[src] ::
   mulIntOp =
   `"*"
dform divIntOp_df : except_mode[src] ::
   divIntOp =
   Nuprl_font!"div"
dform remIntOp_df : except_mode[src] ::
   remIntOp =
   `"%"
dform lslIntOp_df : except_mode[src] ::
   lslIntOp =
   `"<<"
dform lsrIntOp_df : except_mode[src] ::
   lsrIntOp =
   `">>"
dform asrIntOp_df : except_mode[src] ::
   asrIntOp =
   `">>(arith)"
dform andIntOp_df : except_mode[src] ::
   andIntOp =
   `"&"
dform orIntOp_df  : except_mode[src] ::
   orIntOp  =
   `"|"
dform xorIntOp_df : except_mode[src] ::
   xorIntOp =
   `"^"
dform maxIntOp_df : except_mode[src] ::
   maxIntOp =
   `"max"
dform minIntOp_df : except_mode[src] ::
   minIntOp =
   `"min"

dform eqIntOp_df : except_mode[src] ::
   eqIntOp =
   `"="
dform neqIntOp_df : except_mode[src] ::
   neqIntOp =
   `"!="
dform ltIntOp_df : except_mode[src] ::
   ltIntOp =
   `"<"
dform leIntOp_df : except_mode[src] ::
   leIntOp =
   Nuprl_font!le
dform gtIntOp_df : except_mode[src] ::
   gtIntOp =
   `">"
dform geIntOp_df : except_mode[src] ::
   geIntOp =
   Nuprl_font!ge
dform cmpIntOp_df : except_mode[src] ::
   cmpIntOp =
   `"cmp"

(* Native ints. *)

dform plusRawIntOp_df : except_mode[src] ::
   plusRawIntOp{ 'int_precision; 'int_signed } =
   `"(+," slot{'int_precision} `"," slot{'int_signed} `")"
dform minusRawIntOp_df : except_mode[src] ::
   minusRawIntOp{ 'int_precision; 'int_signed } =
   `"(-," slot{'int_precision} `"," slot{'int_signed} `")"
dform mulRawIntOp_df : except_mode[src] ::
   mulRawIntOp{ 'int_precision; 'int_signed } =
   `"(*," slot{'int_precision} `"," slot{'int_signed} `")" ezone
dform divRawIntOp_df : except_mode[src] ::
   divRawIntOp{ 'int_precision; 'int_signed } =
   `"(" Nuprl_font!"div" `"," slot{'int_precision}
   `"," slot{'int_signed} `")"
dform remRawIntOp_df : except_mode[src] ::
   remRawIntOp{ 'int_precision; 'int_signed } =
   `"(%," slot{'int_precision} `"," slot{'int_signed} `")"
dform slRawIntOp_df : except_mode[src] ::
   slRawIntOp{ 'int_precision; 'int_signed } =
   `"(<<," slot{'int_precision} `"," slot{'int_signed} `")"
dform srRawIntOp_df : except_mode[src] ::
   srRawIntOp{ 'int_precision; 'int_signed } =
   `"(>>," slot{'int_precision} `"," slot{'int_signed} `")"
dform andRawIntOp_df : except_mode[src] ::
   andRawIntOp{ 'int_precision; 'int_signed } =
   `"(&," slot{'int_precision} `"," slot{'int_signed} `")"
dform orRawIntOp_df : except_mode[src] ::
   orRawIntOp{ 'int_precision; 'int_signed } =
   `"(|," slot{'int_precision} `"," slot{'int_signed} `")"
dform xorRawIntOp_df : except_mode[src] ::
   xorRawIntOp{ 'int_precision; 'int_signed } =
   `"(^," slot{'int_precision} `"," slot{'int_signed} `")"
dform maxRawIntOp_df : except_mode[src] ::
   maxRawIntOp{ 'int_precision; 'int_signed } =
   `"(max," slot{'int_precision} `"," slot{'int_signed} `")"
dform minRawIntOp_df : except_mode[src] ::
   minRawIntOp{ 'int_precision; 'int_signed } =
   `"(min," slot{'int_precision} `"," slot{'int_signed} `")"

dform rawSetBitFieldOp_df : except_mode[src] ::
   rawSetBitFieldOp{ 'int_precision; 'int_signed; 'int1; 'int2 } =
   `"RawSetBitFieldOp(" slot{'int_precision} `", " slot{'int_signed}
   `", " slot{'int1} `", " slot{'int2} `")"

dform eqRawIntOp_df : except_mode[src] ::
   eqRawIntOp{ 'int_precision; 'int_signed } =
   `"(=," slot{'int_precision} `"," slot{'int_signed} `")"
dform neqRawIntOp_df : except_mode[src] ::
   neqRawIntOp{ 'int_precision; 'int_signed} =
   `"(!=," slot{'int_precision} `"," slot{'int_signed } `")"
dform ltRawIntOp_df : except_mode[src] ::
   ltRawIntOp{ 'int_precision; 'int_signed } =
   `"(<," slot{'int_precision} `"," slot{'int_signed} `")"
dform leRawIntOp_df : except_mode[src] ::
   leRawIntOp{ 'int_precision; 'int_signed } =
   `"(" Nuprl_font!le `"," slot{'int_precision} `"," slot{'int_signed} `")"
dform gtRawIntOp_df : except_mode[src] ::
   gtRawIntOp{ 'int_precision; 'int_signed } =
   `"(>," slot{'int_precision} `"," slot{'int_signed} `")"
dform geRawIntOp_df : except_mode[src] ::
   geRawIntOp{ 'int_precision; 'int_signed } =
   `"(" Nuprl_font!ge `"," slot{'int_precision} `"," slot{'int_signed} `")"
dform cmpRawIntOp_df : except_mode[src] ::
   cmpRawIntOp{ 'int_precision; 'int_signed } =
   `"(cmp," slot{'int_precision} `"," slot{'int_signed} `")"

(* Floats. *)

dform plusFloatOp_df : except_mode[src] ::
   plusFloatOp{ 'float_precision } =
   lzone `"(+," slot{'float_precision} `")" ezone
dform minusFloatOp_df : except_mode[src] ::
   minusFloatOp{ 'float_precision } =
   lzone `"(-," slot{'float_precision} `")" ezone
dform mulFloatOp_df : except_mode[src] ::
   mulFloatOp{ 'float_precision } =
   lzone `"(*," slot{'float_precision} `")" ezone
dform divFloatOp_df : except_mode[src] ::
   divFloatOp{ 'float_precision } =
   lzone `"(" Nuprl_font!"div" `"," slot{'float_precision} `")" ezone
dform remFloatOp_df : except_mode[src] ::
   remFloatOp{ 'float_precision } =
   lzone `"(%," slot{'float_precision} `")" ezone
dform maxFloatOp_df : except_mode[src] ::
   maxFloatOp{ 'float_precision } =
   lzone `"(max," slot{'float_precision} `")" ezone
dform minFloatOp_df : except_mode[src] ::
   minFloatOp{ 'float_precision } =
   lzone `"(min," slot{'float_precision} `")" ezone

dform eqFloatOp_df : except_mode[src] ::
   eqFloatOp{ 'float_precision } =
   lzone `"(=," slot{'float_precision} `")" ezone
dform neqFloatOp_df : except_mode[src] ::
   neqFloatOp{ 'float_precision } =
   lzone `"(!=," slot{'float_precision} `")" ezone
dform ltFloatOp_df : except_mode[src] ::
   ltFloatOp{ 'float_precision } =
   lzone `"(<," slot{'float_precision} `")" ezone
dform leFloatOp_df : except_mode[src] ::
   leFloatOp{ 'float_precision } =
   lzone `"(" Nuprl_font!le `"," slot{'float_precision} `")" ezone
dform gtFloatOp_df : except_mode[src] ::
   gtFloatOp{ 'float_precision } =
   lzone `"(>," slot{'float_precision} `")" ezone
dform geFloatOp_df : except_mode[src] ::
   geFloatOp{ 'float_precision } =
   lzone `"(" Nuprl_font!ge `"," slot{'float_precision} `")" ezone
dform cmpFloatOp_df : except_mode[src] ::
   cmpFloatOp{ 'float_precision } =
   lzone `"(cmp," slot{'float_precision} `")" ezone

dform atan2Op_df : except_mode[src] ::
   atan2Op{ 'float_precision } =
   lzone `"(atan2Op," slot{'float_precision} `")" ezone

(* Pointer equality. *)

dform eqEqOp_df : except_mode[src] ::
   eqEqOp =
   `"EqEqOp"
dform neqEqOp_df : except_mode[src] ::
   neqEqOp =
   `"NeqEqOp"

(* Pointer arithmetic. *)

dform plusPointerOp_df : except_mode[src] ::
   plusPointerOp{ 'sub_block; 'int_precision; 'int_signed } =
   `"PlusPointerOp(" slot{'sub_block} `","
   slot{'int_precision} `"," slot{'int_signed} `")"

(*
 * Fields (frame labels).
 *)

dform frameLabel_df : except_mode[src] ::
   frameLabel{ 'label1; 'label2; 'label3 } =
   `"FrameLabel(" slot{'label1} `"," slot{'label2} `","
   slot{'label3} `")"

(*
 * Normal values.
 *)

dform atomNil_df : except_mode[src] ::
   atomNil{ 'ty } =
   `"AtomNil(" slot{'ty} `")"
dform atomInt_df : except_mode[src] ::
   atomInt{ 'int } =
   `"AtomInt(" slot{'int} `")"
dform atomEnum_df : except_mode[src] ::
   atomEnum{ 'int1; 'int2 } =
   `"AtomEnum(" slot{'int1} `"," slot{'int2} `")"
dform atomRawInt_df : except_mode[src] ::
   atomRawInt{ 'int_precision; 'int_signed; 'num } =
   `"AtomRawInt(" slot{'int_precision} `", "
   slot{'int_signed} `", " slot{'num} `")"
dform atomFloat_df : except_mode[src] ::
   atomFloat{ 'float_precision; 'num } =
   `"AtomFloat(" slot{'float_precision} `", " slot{'num} `")"
dform atomLabel_df : except_mode[src] ::
   atomLabel{ 'frame_label; 'atom_rawint } =
   `"AtomLabel(" slot{'frame_label} `"," slot{'atom_rawint} `")"
dform atomSizeof_df : except_mode[src] ::
   atomSizeof{ 'var_list; 'atom_rawint } =
   `"AtomSizeof(" slot{'var_list} `"," slot{'atom_rawint} `")"
dform atomConst_df : except_mode[src] ::
   atomConst{ 'ty; 'ty_var; 'int } =
   `"AtomConst(" slot{'ty} `", " slot{'ty_var} `", " slot{'int} `")"
dform atomVar_df : except_mode[src] ::
   atomVar{ 'var } =
   `"AtomVar(" slot{'var} `")"

(*
 * Allocation operators.
 *)

dform allocTuple_df : except_mode[src] ::
   allocTuple{ 'tuple_class; 'ty; 'atom_list } =
   `"AllocTuple(" slot{'tuple_class} `"," slot{'ty} `"," slot{'atom_list} `")"
dform allocUnion_df : except_mode[src] ::
   allocUnion{ 'ty; 'ty_var; 'int; 'atom_list } =
   `"AllocUnion(" slot{'ty} `"," slot{'ty_var} `","
   slot{'int} `"," slot{'atom_list} `")"
dform allocArray_df : except_mode[src] :: allocArray{ 'ty; 'atom_list } =
   `"AllocArray(" slot{'ty} `"," slot{'atom_list} `")"
dform allocVArray_df : except_mode[src] ::
   allocVArray{ 'ty; 'sub_index; 'atom1; 'atom2 } =
   `"AllocVArray(" slot{'ty} `"," slot{'sub_index} `","
   slot{'atom1} `"," slot{'atom2} `")"
dform allocMalloc_df : except_mode[src] ::
   allocMalloc{ 'ty; 'atom } =
   `"AllocMalloc(" slot{'ty} `"," slot{'atom} `")"
dform allocFrame_df : except_mode[src] ::
   allocFrame{ 'var } =
   `"AllocFrame(" slot{'var} `")"

(*
 * Tail calls / operations.
 *)

dform tailSysMigrate_df : except_mode[src] ::
   tailSysMigrate{ 'int; 'atom1; 'atom2; 'var; 'atom_list } =
   `"TailSysMigrate(" slot{'int} `"," slot{'atom1} `"," slot{'atom2} `","
   slot{'var} `"," slot{'atom_list} `")"
dform tailAtomic_df : except_mode[src] ::
   tailAtomic{ 'var; 'atom; 'atom_list } =
   `"TailAtom(" slot{'var} `"," slot{'atom} `"," slot{'atom_list} `")"
dform tailAtomicRollBack_df : except_mode[src] ::
   tailAtomicRollback{ 'atom } =
   `"TailAtomicRollback(" slot{'atom} `")"
dform tailAtomicCommit_df : except_mode[src] ::
   tailAtomicCommit{ 'var; 'atom_list } =
   `"TailAtomicCommit(" slot{'var} `"," slot{'atom_list} `")"

(*
 * Predicates and assertions.
 *)

dform isMutable_df : except_mode[src] ::
   isMutable{ 'var } =
   `"IsMutable(" slot{'var} `")"
dform reserve_df : except_mode[src] ::
   reserve{ 'atom1; 'atom2 } =
   `"Reserve(" slot{'atom1} `"," slot{'atom2} `")"
dform boundsCheck_df : except_mode[src] ::
   boundsCheck{ 'subop; 'var; 'atom1; 'atom2 } =
   `"BoundsCheck(" slot{'subop} `"," slot{'var} `","
   slot{'atom1} `"," slot{'atom2} `")"
dform elementCheck_df : except_mode[src] ::
   elementCheck{ 'ty; 'subop; 'var; 'atom } =
   `"ElementCheck(" slot{'ty} `"," slot{'subop} `","
   slot{'var} `"," slot{'atom} `")"

(*
 * Debugging info.
 *)

dform debugLine_df : except_mode[src] ::
   debugLine{ 'string; 'int } =
   `"DebugLine(" slot{'string} `"," slot{'int} `")"
dform debugVarItem_df : except_mode[src] ::
   debugVarItem{ 'var1; 'ty; 'var2 } =
   `"(" slot{'var1} `"," slot{'ty} `"," slot{'var2} `")"
dform debugVars_df : except_mode[src] ::
   debugVars{ 'debugVarItem_list } =
   `"DebugVars(" slot{'debugVarItem_list} `")"
dform debugString_df : except_mode[src] ::
   debugString{ 'string } =
   `"DebugString(" slot{'string} `")"
dform debugContext : except_mode[src] ::
   debugContext{ 'debug_line; 'debug_vars } =
   `"DebugContext(" slot{'debug_line} `"," slot{'debug_vars} `")"

(*
 * Expressions.
 *)

(* Primitive operations. *)

dform letUnop_df : except_mode[src] ::
   letUnop{ 'ty; 'unop; 'atom; var. 'exp } =
   `"LetUnop(" slot{'ty} `"," slot{'unop} `"," slot{'atom} `","
   slot{'var} `". " slot{'exp} `")"
dform letBinop_df : except_mode[src] ::
   letBinop{ 'ty; 'binop; 'atom1; 'atom2; var. 'exp } =
   `"LetBinop(" slot{'ty} `"," slot{'binop} `"," slot{'atom1} `","
   slot{'atom2} `"," slot{'var} `". " slot{'exp} `")"

(* Function application. *)

dform letExt_df : except_mode[src] ::
   letExt{ 'ty1; 'string; 'ty2; 'atom_list; var. 'exp } =
   `"LetExt(" slot{'ty1} `"," slot{'string} `"," slot{'ty2} `","
   slot{'atom_list} `"," slot{'var} `". " slot{'exp} `")"
dform tailCall_df : except_mode[src] ::
   tailCall{ 'label; 'var; 'atom_list } =
   `"TailCall(" slot{'label} `"," slot{'var} `"," slot{'atom_list} `")"
dform specialCall_df : except_mode[src] ::
   specialCall{ 'label; 'tailop } =
   `"SpeciaCall(" slot{'label} `"," slot{'tailop} `")"

(* Control. *)

dform matchCase_df : except_mode[src] ::
   matchCase{ 'label; 'set; 'exp } =
   `"MatchCase(" slot{'label} `"," slot{'set} `"," slot{'exp} `")"
dform matchExp_df : except_mode[src] ::
   matchExp{ 'atom; 'matchCase_list } =
   `"MatchExp(" slot{'atom} `"," slot{'matchCase_list} `")"
dform typeCase_df : except_mode[src] ::
   typeCase{ 'atom1; 'atom2; 'var1; 'var2; 'exp1; 'exp2 } =
   `"TypeCase(" slot{'atom1} `"," slot{'atom2} `"," slot{'var1} `","
   slot{'var2} `"," slot{'exp1} `"," slot{'exp2} `")"

(* Allocation. *)

dform letAlloc_df : except_mode[src] ::
   letAlloc{ 'alloc_op; var. 'exp } =
   `"LetAlloc(" slot{'alloc_op} `"," slot{'var} `". " slot{'exp} `")"

(* Subscripting *)

dform letSubscript_df : except_mode[src] ::
   letSubscript{ 'subop; 'ty; 'var2; 'atom; var1. 'exp } =
   `"LetSubscript(" slot{'subop} `"," slot{'ty} `"," slot{'var2} `","
   slot{'atom} `"," slot{'var1} `". " slot{'exp} `")"
dform setSubscript_df : except_mode[src] ::
   setSubscript{ 'subop; 'label; 'var; 'atom1; 'ty; 'atom2; 'exp } =
   `"SetSubscript(" slot{'subop} `"," slot{'label} `"," slot{'var} `","
   slot{'atom1} `"," slot{'ty} `"," slot{'atom2} `"," slot{'exp} `")"
dform setGlobal_df : except_mode[src] ::
   setGlobal{ 'sub_value; 'label; 'var; 'ty; 'atom; 'exp } =
   `"SetGlobal(" slot{'sub_value} `"," slot{'label} `"," slot{'var} `","
   slot{'ty} `"," slot{'atom} `"," slot{'exp} `")"
dform memcpy_df : except_mode[src] ::
   memcpy{ 'subop; 'label; 'var1; 'atom1; 'var2; 'atom2; 'atom3; 'exp } =
   `"Memcpy(" slot{'subop} `"," slot{'label} `"," slot{'var1} `","
   slot{'atom1} `"," slot{'var2} `"," slot{'atom2} `","
   slot{'atom3} `"," slot{'exp} `")"

(* Assertions. *)

dform call_df : except_mode[src] ::
   call{ 'label; 'var; 'atom_option_list; 'exp } =
   `"Call(" slot{'label} `","
   slot{'var} `"," slot{'atom_option_list} `"," slot{'exp} `")"
dform assertExp_df : except_mode[src] ::
   assertExp{ 'label; 'pred; 'exp } =
   `"AssertExp(" slot{'label} `"," slot{'pred} `"," slot{'exp} `")"

(* Debugging. *)

dform debug_df : except_mode[src] ::
   debug{ 'debug_info; 'exp } =
   `"Debug(" slot{'debug_info} `"," slot{'exp} `")"

(*
 * Function definition.
 *)

dform fundef_df : except_mode[src] ::
   fundef{ 'debug_line; 'ty; 'var_list; 'exp } =
   `"Fundef(" slot{'debug_line} `"," slot{'ty} `","
   slot{'var_list} `"," slot{'exp} `")"

(*************************************************************************
 * Term operations.
 *************************************************************************)

(*
 * Unary operations.
 *)

(* Identity (polymorphic). *)

let idOp_term = << idOp >>
let idOp_opname = opname_of_term idOp_term
let is_idOp_term = is_no_subterms_term idOp_opname

(* Naml ints. *)

let uminusIntOp_term = << uminusIntOp >>
let uminusIntOp_opname = opname_of_term uminusIntOp_term
let is_uminusIntOp_term = is_no_subterms_term uminusIntOp_opname

let notIntOp_term = << notIntOp >>
let notIntOp_opname = opname_of_term notIntOp_term
let is_notIntOp_term = is_no_subterms_term notIntOp_opname

(* Bit fields. *)

let rawBitFieldOp_term = << rawBitFieldOp{ 'precision; 'sign; 'num1; 'num2 } >>
let rawBitFieldOp_opname = opname_of_term rawBitFieldOp_term
let is_rawBitFieldOp_term = is_4_dep0_term rawBitFieldOp_opname
let mk_rawBitFieldOp_term = mk_4_dep0_term rawBitFieldOp_opname
let dest_rawBitFieldOp_term = dest_4_dep0_term rawBitFieldOp_opname

(* Native ints. *)

let uminusRawIntOp_term = << uminusRawIntOp{ 'int_precision; 'int_signed } >>
let uminusRawIntOp_opname = opname_of_term uminusRawIntOp_term
let is_uminusRawIntOp_term = is_dep0_dep0_term uminusRawIntOp_opname
let mk_uminusRawIntOp_term = mk_dep0_dep0_term uminusRawIntOp_opname
let dest_uminusRawIntOp_term = dest_dep0_dep0_term uminusRawIntOp_opname

let notRawIntOp_term = << notRawIntOp{ 'int_precision; 'int_signed } >>
let notRawIntOp_opname = opname_of_term notRawIntOp_term
let is_notRawIntOp_term = is_dep0_dep0_term notRawIntOp_opname
let mk_notRawIntOp_term = mk_dep0_dep0_term notRawIntOp_opname
let dest_notRawIntOp_term = dest_dep0_dep0_term notRawIntOp_opname

(* Floats. *)

let uminusFloatOp_term = << uminusFloatOp{ 'float_precision } >>
let uminusFloatOp_opname = opname_of_term uminusFloatOp_term
let is_uminusFloatOp_term = is_dep0_term uminusFloatOp_opname
let mk_uminusFloatOp_term = mk_dep0_term uminusFloatOp_opname
let dest_uminusFloatOp_term = dest_dep0_term uminusFloatOp_opname

let absFloatOp_term = << absFloatOp{ 'float_precision } >>
let absFloatOp_opname = opname_of_term absFloatOp_term
let is_absFloatOp_term = is_dep0_term absFloatOp_opname
let mk_absFloatOp_term = mk_dep0_term absFloatOp_opname
let dest_absFloatOp_term = dest_dep0_term absFloatOp_opname

let sinOp_term = << sinOp{ 'float_precision } >>
let sinOp_opname = opname_of_term sinOp_term
let is_sinOp_term = is_dep0_term sinOp_opname
let mk_sinOp_term = mk_dep0_term sinOp_opname
let dest_sinOp_term = dest_dep0_term sinOp_opname

let cosOp_term = << cosOp{ 'float_precision } >>
let cosOp_opname = opname_of_term cosOp_term
let is_cosOp_term = is_dep0_term cosOp_opname
let mk_cosOp_term = mk_dep0_term cosOp_opname
let dest_cosOp_term = dest_dep0_term cosOp_opname

let sqrtOp_term = << sqrtOp{ 'float_precision } >>
let sqrtOp_opname = opname_of_term sqrtOp_term
let is_sqrtOp_term = is_dep0_term sqrtOp_opname
let mk_sqrtOp_term = mk_dep0_term sqrtOp_opname
let dest_sqrtOp_term = dest_dep0_term sqrtOp_opname

(* Coerce to int. *)

let intOfFloatOp_term = << intOfFloatOp{ 'float_precision } >>
let intOfFloatOp_opname = opname_of_term intOfFloatOp_term
let is_intOfFloatOp_term = is_dep0_term intOfFloatOp_opname
let mk_intOfFloatOp_term = mk_dep0_term intOfFloatOp_opname
let dest_intOfFloatOp_term = dest_dep0_term intOfFloatOp_opname

(* Coerce to float. *)

let floatOfIntOp_term = << floatOfIntOp{ 'precision } >>
let floatOfIntOp_opname = opname_of_term floatOfIntOp_term
let is_floatOfIntOp_term = is_dep0_term floatOfIntOp_opname
let mk_floatOfIntOp_term = mk_dep0_term floatOfIntOp_opname
let dest_floatOfIntOp_term = dest_dep0_term floatOfIntOp_opname

let floatOfFloatOp_term = << floatOfFloatOp{ 'prec1; 'prec2 } >>
let floatOfFloatOp_opname = opname_of_term floatOfFloatOp_term
let is_floatOfFloatOp_term = is_dep0_dep0_term floatOfFloatOp_opname
let mk_floatOfFloatOp_term = mk_dep0_dep0_term floatOfFloatOp_opname
let dest_floatOfFloatOp_term = dest_dep0_dep0_term floatOfFloatOp_opname

let floatOfRawIntOp_term =
   << floatOfRawIntOp{ 'float_prec; 'int_prec; 'int_sign } >>
let floatOfRawIntOp_opname = opname_of_term floatOfRawIntOp_term
let is_floatOfRawIntOp_term = is_dep0_dep0_dep0_term floatOfRawIntOp_opname
let mk_floatOfRawIntOp_term = mk_dep0_dep0_dep0_term floatOfRawIntOp_opname
let dest_floatOfRawIntOp_term = dest_dep0_dep0_dep0_term floatOfRawIntOp_opname

(* Coerce to rawint. *)

let rawIntOfIntOp_term = << rawIntOfIntOp{ 'int_precision; 'int_signed } >>
let rawIntOfIntOp_opname = opname_of_term rawIntOfIntOp_term
let is_rawIntOfIntOp_term = is_dep0_dep0_term rawIntOfIntOp_opname
let mk_rawIntOfIntOp_term = mk_dep0_dep0_term rawIntOfIntOp_opname
let dest_rawIntOfIntOp_term = dest_dep0_dep0_term rawIntOfIntOp_opname

let rawIntOfEnumOp_term =
   << rawIntOfEnumOp{ 'int_precision; 'int_signed; 'int } >>
let rawIntOfEnumOp_opname = opname_of_term rawIntOfEnumOp_term
let is_rawIntOfEnumOp_term = is_dep0_dep0_dep0_term rawIntOfEnumOp_opname
let mk_rawIntOfEnumOp_term = mk_dep0_dep0_dep0_term rawIntOfEnumOp_opname
let dest_rawIntOfEnumOp_term = dest_dep0_dep0_dep0_term rawIntOfEnumOp_opname

let rawIntOfFloatOp_term =
   << rawIntOfFloatOp{ 'int_precision; 'int_signed; 'float_precision } >>
let rawIntOfFloatOp_opname = opname_of_term rawIntOfFloatOp_term
let is_rawIntOfFloatOp_term = is_dep0_dep0_dep0_term rawIntOfFloatOp_opname
let mk_rawIntOfFloatOp_term = mk_dep0_dep0_dep0_term rawIntOfFloatOp_opname
let dest_rawIntOfFloatOp_term = dest_dep0_dep0_dep0_term rawIntOfFloatOp_opname

let rawIntOfRawIntOp_term =
   << rawIntOfRawIntOp{ 'dest_int_precision; 'dest_int_signed;
                        'src_int_precision;  'src_int_signed } >>
let rawIntOfRawIntOp_opname = opname_of_term rawIntOfRawIntOp_term
let is_rawIntOfRawIntOp_term = is_4_dep0_term rawIntOfRawIntOp_opname
let mk_rawIntOfRawIntOp_term = mk_4_dep0_term rawIntOfRawIntOp_opname
let dest_rawIntOfRawIntOp_term = dest_4_dep0_term rawIntOfRawIntOp_opname

(* Integer/pointer coercions. *)

let rawIntOfPointerOp_term =
   << rawIntOfPointerOp{ 'int_precision; 'int_signed } >>
let rawIntOfPointerOp_opname = opname_of_term rawIntOfPointerOp_term
let is_rawIntOfPointerOp_term = is_dep0_dep0_term rawIntOfPointerOp_opname
let mk_rawIntOfPointerOp_term = mk_dep0_dep0_term rawIntOfPointerOp_opname
let dest_rawIntOfPointerOp_term = dest_dep0_dep0_term rawIntOfPointerOp_opname

let pointerOfRawIntOp_term =
   << pointerOfRawIntOp{ 'int_precision; 'int_signed } >>
let pointerOfRawIntOp_opname = opname_of_term pointerOfRawIntOp_term
let is_pointerOfRawIntOp_term = is_dep0_dep0_term pointerOfRawIntOp_opname
let mk_pointerOfRawIntOp_term = mk_dep0_dep0_term pointerOfRawIntOp_opname
let dest_pointerOfRawIntOp_term = dest_dep0_dep0_term pointerOfRawIntOp_opname

(* Pointer from a block pointer. *)

let pointerOfBlockOp_term = << pointerOfBlockOp{ 'sub_block } >>
let pointerOfBlockOp_opname = opname_of_term pointerOfBlockOp_term
let is_pointerOfBlockOp_term = is_dep0_term pointerOfBlockOp_opname
let mk_pointerOfBlockOp_term = mk_dep0_term pointerOfBlockOp_opname
let dest_pointerOfBlockOp_term = dest_dep0_term pointerOfBlockOp_opname

(*
 * Binary operations.
 *)

(* Enums. *)

let andEnumOp_term = << andEnumOp{ 'num } >>
let andEnumOp_opname = opname_of_term andEnumOp_term
let is_andEnumOp_term = is_dep0_term andEnumOp_opname
let mk_andEnumOp_term = mk_dep0_term andEnumOp_opname
let dest_andEnumOp_term = dest_dep0_term andEnumOp_opname

let orEnumOp_term = << orEnumOp{ 'num } >>
let orEnumOp_opname = opname_of_term orEnumOp_term
let is_orEnumOp_term = is_dep0_term orEnumOp_opname
let mk_orEnumOp_term = mk_dep0_term orEnumOp_opname
let dest_orEnumOp_term = dest_dep0_term orEnumOp_opname

let xorEnumOp_term = << xorEnumOp{ 'num } >>
let xorEnumOp_opname = opname_of_term xorEnumOp_term
let is_xorEnumOp_term = is_dep0_term xorEnumOp_opname
let mk_xorEnumOp_term = mk_dep0_term xorEnumOp_opname
let dest_xorEnumOp_term = dest_dep0_term xorEnumOp_opname

(* Naml ints. *)

let plusIntOp_term = << plusIntOp >>
let plusIntOp_opname = opname_of_term plusIntOp_term
let is_plusIntOp_term = is_no_subterms_term plusIntOp_opname

let minusIntOp_term = << minusIntOp >>
let minusIntOp_opname = opname_of_term minusIntOp_term
let is_minusIntOp_term = is_no_subterms_term minusIntOp_opname

let mulIntOp_term = << mulIntOp >>
let mulIntOp_opname = opname_of_term mulIntOp_term
let is_mulIntOp_term = is_no_subterms_term mulIntOp_opname

let divIntOp_term = << divIntOp >>
let divIntOp_opname = opname_of_term divIntOp_term
let is_divIntOp_term = is_no_subterms_term divIntOp_opname

let remIntOp_term = << remIntOp >>
let remIntOp_opname = opname_of_term remIntOp_term
let is_remIntOp_term = is_no_subterms_term remIntOp_opname

let lslIntOp_term = << lslIntOp >>
let lslIntOp_opname = opname_of_term lslIntOp_term
let is_lslIntOp_term = is_no_subterms_term lslIntOp_opname

let lsrIntOp_term = << lsrIntOp >>
let lsrIntOp_opname = opname_of_term lsrIntOp_term
let is_lsrIntOp_term = is_no_subterms_term lsrIntOp_opname

let asrIntOp_term = << asrIntOp >>
let asrIntOp_opname = opname_of_term asrIntOp_term
let is_asrIntOp_term = is_no_subterms_term asrIntOp_opname

let andIntOp_term = << andIntOp >>
let andIntOp_opname = opname_of_term andIntOp_term
let is_andIntOp_term = is_no_subterms_term andIntOp_opname

let orIntOp_term = << orIntOp >>
let orIntOp_opname = opname_of_term orIntOp_term
let is_orIntOp_term = is_no_subterms_term orIntOp_opname

let xorIntOp_term = << xorIntOp >>
let xorIntOp_opname = opname_of_term xorIntOp_term
let is_xorIntOp_term = is_no_subterms_term xorIntOp_opname

let maxIntOp_term = << maxIntOp >>
let maxIntOp_opname = opname_of_term maxIntOp_term
let is_maxIntOp_term = is_no_subterms_term maxIntOp_opname

let minIntOp_term = << minIntOp >>
let minIntOp_opname = opname_of_term minIntOp_term
let is_minIntOp_term = is_no_subterms_term minIntOp_opname

let eqIntOp_term = << eqIntOp >>
let eqIntOp_opname = opname_of_term eqIntOp_term
let is_eqIntOp_term = is_no_subterms_term eqIntOp_opname

let neqIntOp_term = << neqIntOp >>
let neqIntOp_opname = opname_of_term neqIntOp_term
let is_neqIntOp_term = is_no_subterms_term neqIntOp_opname

let ltIntOp_term = << ltIntOp >>
let ltIntOp_opname = opname_of_term ltIntOp_term
let is_ltIntOp_term = is_no_subterms_term ltIntOp_opname

let leIntOp_term = << leIntOp >>
let leIntOp_opname = opname_of_term leIntOp_term
let is_leIntOp_term = is_no_subterms_term leIntOp_opname

let gtIntOp_term = << gtIntOp >>
let gtIntOp_opname = opname_of_term gtIntOp_term
let is_gtIntOp_term = is_no_subterms_term gtIntOp_opname

let geIntOp_term = << geIntOp >>
let geIntOp_opname = opname_of_term geIntOp_term
let is_geIntOp_term = is_no_subterms_term geIntOp_opname

let cmpIntOp_term = << cmpIntOp >>
let cmpIntOp_opname = opname_of_term cmpIntOp_term
let is_cmpIntOp_term = is_no_subterms_term cmpIntOp_opname

(* Native ints. *)

let plusRawIntOp_term = << plusRawIntOp{ 'int_precision; 'int_signed } >>
let plusRawIntOp_opname = opname_of_term plusRawIntOp_term
let is_plusRawIntOp_term = is_dep0_dep0_term plusRawIntOp_opname
let mk_plusRawIntOp_term = mk_dep0_dep0_term plusRawIntOp_opname
let dest_plusRawIntOp_term = dest_dep0_dep0_term plusRawIntOp_opname

let minusRawIntOp_term = << minusRawIntOp{ 'int_precision; 'int_signed } >>
let minusRawIntOp_opname = opname_of_term minusRawIntOp_term
let is_minusRawIntOp_term = is_dep0_dep0_term minusRawIntOp_opname
let mk_minusRawIntOp_term = mk_dep0_dep0_term minusRawIntOp_opname
let dest_minusRawIntOp_term = dest_dep0_dep0_term minusRawIntOp_opname

let mulRawIntOp_term = << mulRawIntOp{ 'int_precision; 'int_signed } >>
let mulRawIntOp_opname = opname_of_term mulRawIntOp_term
let is_mulRawIntOp_term = is_dep0_dep0_term mulRawIntOp_opname
let mk_mulRawIntOp_term = mk_dep0_dep0_term mulRawIntOp_opname
let dest_mulRawIntOp_term = dest_dep0_dep0_term mulRawIntOp_opname

let divRawIntOp_term = << divRawIntOp{ 'int_precision; 'int_signed } >>
let divRawIntOp_opname = opname_of_term divRawIntOp_term
let is_divRawIntOp_term = is_dep0_dep0_term divRawIntOp_opname
let mk_divRawIntOp_term = mk_dep0_dep0_term divRawIntOp_opname
let dest_divRawIntOp_term = dest_dep0_dep0_term divRawIntOp_opname

let remRawIntOp_term = << remRawIntOp{ 'int_precision; 'int_signed } >>
let remRawIntOp_opname = opname_of_term remRawIntOp_term
let is_remRawIntOp_term = is_dep0_dep0_term remRawIntOp_opname
let mk_remRawIntOp_term = mk_dep0_dep0_term remRawIntOp_opname
let dest_remRawIntOp_term = dest_dep0_dep0_term remRawIntOp_opname

let slRawIntOp_term = << slRawIntOp{ 'int_precision; 'int_signed } >>
let slRawIntOp_opname = opname_of_term slRawIntOp_term
let is_slRawIntOp_term = is_dep0_dep0_term slRawIntOp_opname
let mk_slRawIntOp_term = mk_dep0_dep0_term slRawIntOp_opname
let dest_slRawIntOp_term = dest_dep0_dep0_term slRawIntOp_opname

let srRawIntOp_term = << srRawIntOp{ 'int_precision; 'int_signed } >>
let srRawIntOp_opname = opname_of_term srRawIntOp_term
let is_srRawIntOp_term = is_dep0_dep0_term srRawIntOp_opname
let mk_srRawIntOp_term = mk_dep0_dep0_term srRawIntOp_opname
let dest_srRawIntOp_term = dest_dep0_dep0_term srRawIntOp_opname

let andRawIntOp_term = << andRawIntOp{ 'int_precision; 'int_signed } >>
let andRawIntOp_opname = opname_of_term andRawIntOp_term
let is_andRawIntOp_term = is_dep0_dep0_term andRawIntOp_opname
let mk_andRawIntOp_term = mk_dep0_dep0_term andRawIntOp_opname
let dest_andRawIntOp_term = dest_dep0_dep0_term andRawIntOp_opname

let orRawIntOp_term = << orRawIntOp{ 'int_precision; 'int_signed } >>
let orRawIntOp_opname = opname_of_term orRawIntOp_term
let is_orRawIntOp_term = is_dep0_dep0_term orRawIntOp_opname
let mk_orRawIntOp_term = mk_dep0_dep0_term orRawIntOp_opname
let dest_orRawIntOp_term = dest_dep0_dep0_term orRawIntOp_opname

let xorRawIntOp_term = << xorRawIntOp{ 'int_precision; 'int_signed } >>
let xorRawIntOp_opname = opname_of_term xorRawIntOp_term
let is_xorRawIntOp_term = is_dep0_dep0_term xorRawIntOp_opname
let mk_xorRawIntOp_term = mk_dep0_dep0_term xorRawIntOp_opname
let dest_xorRawIntOp_term = dest_dep0_dep0_term xorRawIntOp_opname

let maxRawIntOp_term = << maxRawIntOp{ 'int_precision; 'int_signed } >>
let maxRawIntOp_opname = opname_of_term maxRawIntOp_term
let is_maxRawIntOp_term = is_dep0_dep0_term maxRawIntOp_opname
let mk_maxRawIntOp_term = mk_dep0_dep0_term maxRawIntOp_opname
let dest_maxRawIntOp_term = dest_dep0_dep0_term maxRawIntOp_opname

let minRawIntOp_term = << minRawIntOp{ 'int_precision; 'int_signed } >>
let minRawIntOp_opname = opname_of_term minRawIntOp_term
let is_minRawIntOp_term = is_dep0_dep0_term minRawIntOp_opname
let mk_minRawIntOp_term = mk_dep0_dep0_term minRawIntOp_opname
let dest_minRawIntOp_term = dest_dep0_dep0_term minRawIntOp_opname

let rawSetBitFieldOp_term =
   << rawSetBitFieldOp{ 'int_precision; 'int_signed ; 'int1; 'int2 } >>
let rawSetBitFieldOp_opname = opname_of_term rawSetBitFieldOp_term
let is_rawSetBitFieldOp_term = is_4_dep0_term rawSetBitFieldOp_opname
let mk_rawSetBitFieldOp_term = mk_4_dep0_term rawSetBitFieldOp_opname
let dest_rawSetBitFieldOp_term = dest_4_dep0_term rawSetBitFieldOp_opname

let eqRawIntOp_term = << eqRawIntOp{ 'int_precision; 'int_signed } >>
let eqRawIntOp_opname = opname_of_term eqRawIntOp_term
let is_eqRawIntOp_term = is_dep0_dep0_term eqRawIntOp_opname
let mk_eqRawIntOp_term = mk_dep0_dep0_term eqRawIntOp_opname
let dest_eqRawIntOp_term = dest_dep0_dep0_term eqRawIntOp_opname

let neqRawIntOp_term = << neqRawIntOp{ 'int_precision; 'int_signed } >>
let neqRawIntOp_opname = opname_of_term neqRawIntOp_term
let is_neqRawIntOp_term = is_dep0_dep0_term neqRawIntOp_opname
let mk_neqRawIntOp_term = mk_dep0_dep0_term neqRawIntOp_opname
let dest_neqRawIntOp_term = dest_dep0_dep0_term neqRawIntOp_opname

let ltRawIntOp_term = << ltRawIntOp{ 'int_precision; 'int_signed } >>
let ltRawIntOp_opname = opname_of_term ltRawIntOp_term
let is_ltRawIntOp_term = is_dep0_dep0_term ltRawIntOp_opname
let mk_ltRawIntOp_term = mk_dep0_dep0_term ltRawIntOp_opname
let dest_ltRawIntOp_term = dest_dep0_dep0_term ltRawIntOp_opname

let leRawIntOp_term = << leRawIntOp{ 'int_precision; 'int_signed } >>
let leRawIntOp_opname = opname_of_term leRawIntOp_term
let is_leRawIntOp_term = is_dep0_dep0_term leRawIntOp_opname
let mk_leRawIntOp_term = mk_dep0_dep0_term leRawIntOp_opname
let dest_leRawIntOp_term = dest_dep0_dep0_term leRawIntOp_opname

let gtRawIntOp_term = << gtRawIntOp{ 'int_precision; 'int_signed } >>
let gtRawIntOp_opname = opname_of_term gtRawIntOp_term
let is_gtRawIntOp_term = is_dep0_dep0_term gtRawIntOp_opname
let mk_gtRawIntOp_term = mk_dep0_dep0_term gtRawIntOp_opname
let dest_gtRawIntOp_term = dest_dep0_dep0_term gtRawIntOp_opname

let geRawIntOp_term = << geRawIntOp{ 'int_precision; 'int_signed } >>
let geRawIntOp_opname = opname_of_term geRawIntOp_term
let is_geRawIntOp_term = is_dep0_dep0_term geRawIntOp_opname
let mk_geRawIntOp_term = mk_dep0_dep0_term geRawIntOp_opname
let dest_geRawIntOp_term = dest_dep0_dep0_term geRawIntOp_opname

let cmpRawIntOp_term = << cmpRawIntOp{ 'int_precision; 'int_signed } >>
let cmpRawIntOp_opname = opname_of_term cmpRawIntOp_term
let is_cmpRawIntOp_term = is_dep0_dep0_term cmpRawIntOp_opname
let mk_cmpRawIntOp_term = mk_dep0_dep0_term cmpRawIntOp_opname
let dest_cmpRawIntOp_term = dest_dep0_dep0_term cmpRawIntOp_opname

(* Floats. *)

let plusFloatOp_term = << plusFloatOp{ 'float_precision } >>
let plusFloatOp_opname = opname_of_term plusFloatOp_term
let is_plusFloatOp_term = is_dep0_term plusFloatOp_opname
let mk_plusFloatOp_term = mk_dep0_term plusFloatOp_opname
let dest_plusFloatOp_term = dest_dep0_term plusFloatOp_opname

let minusFloatOp_term = << minusFloatOp{ 'float_precision } >>
let minusFloatOp_opname = opname_of_term minusFloatOp_term
let is_minusFloatOp_term = is_dep0_term minusFloatOp_opname
let mk_minusFloatOp_term = mk_dep0_term minusFloatOp_opname
let dest_minusFloatOp_term = dest_dep0_term minusFloatOp_opname

let mulFloatOp_term = << mulFloatOp{ 'float_precision } >>
let mulFloatOp_opname = opname_of_term mulFloatOp_term
let is_mulFloatOp_term = is_dep0_term mulFloatOp_opname
let mk_mulFloatOp_term = mk_dep0_term mulFloatOp_opname
let dest_mulFloatOp_term = dest_dep0_term mulFloatOp_opname

let divFloatOp_term = << divFloatOp{ 'float_precision } >>
let divFloatOp_opname = opname_of_term divFloatOp_term
let is_divFloatOp_term = is_dep0_term divFloatOp_opname
let mk_divFloatOp_term = mk_dep0_term divFloatOp_opname
let dest_divFloatOp_term = dest_dep0_term divFloatOp_opname

let remFloatOp_term = << remFloatOp{ 'float_precision } >>
let remFloatOp_opname = opname_of_term remFloatOp_term
let is_remFloatOp_term = is_dep0_term remFloatOp_opname
let mk_remFloatOp_term = mk_dep0_term remFloatOp_opname
let dest_remFloatOp_term = dest_dep0_term remFloatOp_opname

let maxFloatOp_term = << maxFloatOp{ 'float_precision } >>
let maxFloatOp_opname = opname_of_term maxFloatOp_term
let is_maxFloatOp_term = is_dep0_term maxFloatOp_opname
let mk_maxFloatOp_term = mk_dep0_term maxFloatOp_opname
let dest_maxFloatOp_term = dest_dep0_term maxFloatOp_opname

let minFloatOp_term = << minFloatOp{ 'float_precision } >>
let minFloatOp_opname = opname_of_term minFloatOp_term
let is_minFloatOp_term = is_dep0_term minFloatOp_opname
let mk_minFloatOp_term = mk_dep0_term minFloatOp_opname
let dest_minFloatOp_term = dest_dep0_term minFloatOp_opname

let eqFloatOp_term = << eqFloatOp{ 'float_precision } >>
let eqFloatOp_opname = opname_of_term eqFloatOp_term
let is_eqFloatOp_term = is_dep0_term eqFloatOp_opname
let mk_eqFloatOp_term = mk_dep0_term eqFloatOp_opname
let dest_eqFloatOp_term = dest_dep0_term eqFloatOp_opname

let neqFloatOp_term = << neqFloatOp{ 'float_precision } >>
let neqFloatOp_opname = opname_of_term neqFloatOp_term
let is_neqFloatOp_term = is_dep0_term neqFloatOp_opname
let mk_neqFloatOp_term = mk_dep0_term neqFloatOp_opname
let dest_neqFloatOp_term = dest_dep0_term neqFloatOp_opname

let ltFloatOp_term = << ltFloatOp{ 'float_precision } >>
let ltFloatOp_opname = opname_of_term ltFloatOp_term
let is_ltFloatOp_term = is_dep0_term ltFloatOp_opname
let mk_ltFloatOp_term = mk_dep0_term ltFloatOp_opname
let dest_ltFloatOp_term = dest_dep0_term ltFloatOp_opname

let leFloatOp_term = << leFloatOp{ 'float_precision } >>
let leFloatOp_opname = opname_of_term leFloatOp_term
let is_leFloatOp_term = is_dep0_term leFloatOp_opname
let mk_leFloatOp_term = mk_dep0_term leFloatOp_opname
let dest_leFloatOp_term = dest_dep0_term leFloatOp_opname

let gtFloatOp_term = << gtFloatOp{ 'float_precision } >>
let gtFloatOp_opname = opname_of_term gtFloatOp_term
let is_gtFloatOp_term = is_dep0_term gtFloatOp_opname
let mk_gtFloatOp_term = mk_dep0_term gtFloatOp_opname
let dest_gtFloatOp_term = dest_dep0_term gtFloatOp_opname

let geFloatOp_term = << geFloatOp{ 'float_precision } >>
let geFloatOp_opname = opname_of_term geFloatOp_term
let is_geFloatOp_term = is_dep0_term geFloatOp_opname
let mk_geFloatOp_term = mk_dep0_term geFloatOp_opname
let dest_geFloatOp_term = dest_dep0_term geFloatOp_opname

let cmpFloatOp_term = << cmpFloatOp{ 'float_precision } >>
let cmpFloatOp_opname = opname_of_term cmpFloatOp_term
let is_cmpFloatOp_term = is_dep0_term cmpFloatOp_opname
let mk_cmpFloatOp_term = mk_dep0_term cmpFloatOp_opname
let dest_cmpFloatOp_term = dest_dep0_term cmpFloatOp_opname

let atan2Op_term = << atan2Op{ 'float_precision } >>
let atan2Op_opname = opname_of_term atan2Op_term
let is_atan2Op_term = is_dep0_term atan2Op_opname
let mk_atan2Op_term = mk_dep0_term atan2Op_opname
let dest_atan2Op_term = dest_dep0_term atan2Op_opname

(* Pointer equality. *)

let eqEqOp_term = << eqEqOp >>
let eqEqOp_opname = opname_of_term eqEqOp_term
let is_eqEqOp_term = is_no_subterms_term eqEqOp_opname

let neqEqOp_term = << neqEqOp >>
let neqEqOp_opname = opname_of_term neqEqOp_term
let is_neqEqOp_term = is_no_subterms_term neqEqOp_opname

(* Pointer arithmetic. *)

let plusPointerOp_term =
   << plusPointerOp{ 'sub_block; 'int_precision; 'int_signed } >>
let plusPointerOp_opname = opname_of_term plusPointerOp_term
let is_plusPointerOp_term = is_dep0_dep0_dep0_term plusPointerOp_opname
let mk_plusPointerOp_term = mk_dep0_dep0_dep0_term plusPointerOp_opname
let dest_plusPointerOp_term = dest_dep0_dep0_dep0_term plusPointerOp_opname

(*
 * Fields (frame labels).
 *)

let frameLabel_term = << frameLabel{ 'label1; 'label2; 'label3 } >>
let frameLabel_opname = opname_of_term frameLabel_term
let is_frameLabel_term = is_dep0_dep0_dep0_term frameLabel_opname
let mk_frameLabel_term = mk_dep0_dep0_dep0_term frameLabel_opname
let dest_frameLabel_term = dest_dep0_dep0_dep0_term frameLabel_opname

(*
 * Normal values.
 *)

let atomNil_term = << atomNil{ 'ty } >>
let atomNil_opname = opname_of_term atomNil_term
let is_atomNil_term = is_dep0_term atomNil_opname
let mk_atomNil_term = mk_dep0_term atomNil_opname
let dest_atomNil_term = dest_dep0_term atomNil_opname

let atomInt_term = << atomInt{ 'int } >>
let atomInt_opname = opname_of_term atomInt_term
let is_atomInt_term = is_dep0_term atomInt_opname
let mk_atomInt_term = mk_dep0_term atomInt_opname
let dest_atomInt_term = dest_dep0_term atomInt_opname

let atomEnum_term = << atomEnum{ 'int1; 'int2 } >>
let atomEnum_opname = opname_of_term atomEnum_term
let is_atomEnum_term = is_dep0_dep0_term atomEnum_opname
let mk_atomEnum_term = mk_dep0_dep0_term atomEnum_opname
let dest_atomEnum_term = dest_dep0_dep0_term atomEnum_opname

let atomRawInt_term = << atomRawInt{ 'int_precision; 'int_signed; 'num } >>
let atomRawInt_opname = opname_of_term atomRawInt_term
let is_atomRawInt_term = is_dep0_dep0_dep0_term atomRawInt_opname
let mk_atomRawInt_term = mk_dep0_dep0_dep0_term atomRawInt_opname
let dest_atomRawInt_term = dest_dep0_dep0_dep0_term atomRawInt_opname

let atomFloat_term = << atomFloat{ 'float_precision; 'num } >>
let atomFloat_opname = opname_of_term atomFloat_term
let is_atomFloat_term = is_dep0_dep0_term atomFloat_opname
let mk_atomFloat_term = mk_dep0_dep0_term atomFloat_opname
let dest_atomFloat_term = dest_dep0_dep0_term atomFloat_opname

let atomLabel_term = << atomLabel{ 'frame_label; 'atom_rawint } >>
let atomLabel_opname = opname_of_term atomLabel_term
let is_atomLabel_term = is_dep0_dep0_term atomLabel_opname
let mk_atomLabel_term = mk_dep0_dep0_term atomLabel_opname
let dest_atomLabel_term = dest_dep0_dep0_term atomLabel_opname

let atomSizeof_term = << atomSizeof{ 'var_list; 'atom_rawint } >>
let atomSizeof_opname = opname_of_term atomSizeof_term
let is_atomSizeof_term = is_dep0_dep0_term atomSizeof_opname
let mk_atomSizeof_term = mk_dep0_dep0_term atomSizeof_opname
let dest_atomSizeof_term = dest_dep0_dep0_term atomSizeof_opname

let atomConst_term = << atomConst{ 'ty; 'ty_var; 'int } >>
let atomConst_opname = opname_of_term atomConst_term
let is_atomConst_term = is_dep0_dep0_dep0_term atomConst_opname
let mk_atomConst_term = mk_dep0_dep0_dep0_term atomConst_opname
let dest_atomConst_term = dest_dep0_dep0_dep0_term atomConst_opname

let atomVar_term = << atomVar{ 'var } >>
let atomVar_opname = opname_of_term atomVar_term
let is_atomVar_term = is_dep0_term atomVar_opname
let mk_atomVar_term = mk_dep0_term atomVar_opname
let dest_atomVar_term = dest_dep0_term atomVar_opname

(*
 * Allocation operators.
 *)

let allocTuple_term = << allocTuple{ 'tuple_class; 'ty; 'atom_list } >>
let allocTuple_opname = opname_of_term allocTuple_term
let is_allocTuple_term = is_dep0_dep0_dep0_term allocTuple_opname
let mk_allocTuple_term = mk_dep0_dep0_dep0_term allocTuple_opname
let dest_allocTuple_term = dest_dep0_dep0_dep0_term allocTuple_opname

let allocUnion_term = << allocUnion{ 'ty; 'ty_var; 'int; 'atom_list } >>
let allocUnion_opname = opname_of_term allocUnion_term
let is_allocUnion_term = is_4_dep0_term allocUnion_opname
let mk_allocUnion_term = mk_4_dep0_term allocUnion_opname
let dest_allocUnion_term = dest_4_dep0_term allocUnion_opname

let allocArray_term = << allocArray{ 'ty; 'atom_list } >>
let allocArray_opname = opname_of_term allocArray_term
let is_allocArray_term = is_dep0_dep0_term allocArray_opname
let mk_allocArray_term = mk_dep0_dep0_term allocArray_opname
let dest_allocArray_term = dest_dep0_dep0_term allocArray_opname

let allocVArray_term = << allocVArray{ 'ty; 'sub_index; 'atom1; 'atom2 } >>
let allocVArray_opname = opname_of_term allocVArray_term
let is_allocVArray_term = is_4_dep0_term allocVArray_opname
let mk_allocVArray_term = mk_4_dep0_term allocVArray_opname
let dest_allocVArray_term = dest_4_dep0_term allocVArray_opname

let allocMalloc_term = << allocMalloc{ 'ty; 'atom } >>
let allocMalloc_opname = opname_of_term allocMalloc_term
let is_allocMalloc_term = is_dep0_dep0_term allocMalloc_opname
let mk_allocMalloc_term = mk_dep0_dep0_term allocMalloc_opname
let dest_allocMalloc_term = dest_dep0_dep0_term allocMalloc_opname

let allocFrame_term = << allocFrame{ 'var } >>
let allocFrame_opname = opname_of_term allocFrame_term
let is_allocFrame_term = is_dep0_term allocFrame_opname
let mk_allocFrame_term = mk_dep0_term allocFrame_opname
let dest_allocFrame_term = dest_dep0_term allocFrame_opname

(*
 * Tail calls / operations.
 *)

let tailSysMigrate_term =
   << tailSysMigrate{ 'int; 'atom1; 'atom2; 'var; 'atom_list } >>
let tailSysMigrate_opname = opname_of_term tailSysMigrate_term
let is_tailSysMigrate_term = is_5_dep0_term tailSysMigrate_opname
let mk_tailSysMigrate_term = mk_5_dep0_term tailSysMigrate_opname
let dest_tailSysMigrate_term = dest_5_dep0_term tailSysMigrate_opname

let tailAtomic_term = << tailAtomic{ 'var; 'atom; 'atom_list } >>
let tailAtomic_opname = opname_of_term tailAtomic_term
let is_tailAtomic_term = is_dep0_dep0_dep0_term tailAtomic_opname
let mk_tailAtomic_term = mk_dep0_dep0_dep0_term tailAtomic_opname
let dest_tailAtomic_term = dest_dep0_dep0_dep0_term tailAtomic_opname

let tailAtomicRollback_term = << tailAtomicRollback{ 'atom } >>
let tailAtomicRollback_opname = opname_of_term tailAtomicRollback_term
let is_tailAtomicRollback_term = is_dep0_term tailAtomicRollback_opname
let mk_tailAtomicRollback_term = mk_dep0_term tailAtomicRollback_opname
let dest_tailAtomicRollback_term = dest_dep0_term tailAtomicRollback_opname

let tailAtomicCommit_term = << tailAtomicCommit{ 'var; 'atom_list } >>
let tailAtomicCommit_opname = opname_of_term tailAtomicCommit_term
let is_tailAtomicCommit_term = is_dep0_dep0_term tailAtomicCommit_opname
let mk_tailAtomicCommit_term = mk_dep0_dep0_term tailAtomicCommit_opname
let dest_tailAtomicCommit_term = dest_dep0_dep0_term tailAtomicCommit_opname

(*
 * Predicates and assertions.
 *)

let isMutable_term = << isMutable{ 'var } >>
let isMutable_opname = opname_of_term isMutable_term
let is_isMutable_term = is_dep0_term isMutable_opname
let mk_isMutable_term = mk_dep0_term isMutable_opname
let dest_isMutable_term = dest_dep0_term isMutable_opname

let reserve_term = << reserve{ 'atom1; 'atom2 } >>
let reserve_opname = opname_of_term reserve_term
let is_reserve_term = is_dep0_dep0_term reserve_opname
let mk_reserve_term = mk_dep0_dep0_term reserve_opname
let dest_reserve_term = dest_dep0_dep0_term reserve_opname

let boundsCheck_term = << boundsCheck{ 'subop; 'var; 'atom1; 'atom2 } >>
let boundsCheck_opname = opname_of_term boundsCheck_term
let is_boundsCheck_term = is_4_dep0_term boundsCheck_opname
let mk_boundsCheck_term = mk_4_dep0_term boundsCheck_opname
let dest_boundsCheck_term = dest_4_dep0_term boundsCheck_opname

let elementCheck_term = << elementCheck{ 'ty; 'subop; 'var; 'atom } >>
let elementCheck_opname = opname_of_term elementCheck_term
let is_elementCheck_term = is_4_dep0_term elementCheck_opname
let mk_elementCheck_term = mk_4_dep0_term elementCheck_opname
let dest_elementCheck_term = dest_4_dep0_term elementCheck_opname

(*
 * Debugging info.
 *)

let debugLine_term = << debugLine{ 'string; 'int } >>
let debugLine_opname = opname_of_term debugLine_term
let is_debugLine_term = is_dep0_dep0_term debugLine_opname
let mk_debugLine_term = mk_dep0_dep0_term debugLine_opname
let dest_debugLine_term = dest_dep0_dep0_term debugLine_opname

let debugVarItem_term = << debugVarItem{ 'var1; 'ty; 'var2 } >>
let debugVarItem_opname = opname_of_term debugVarItem_term
let is_debugVarItem_term = is_dep0_dep0_dep0_term debugVarItem_opname
let mk_debugVarItem_term = mk_dep0_dep0_dep0_term debugVarItem_opname
let dest_debugVarItem_term = dest_dep0_dep0_dep0_term debugVarItem_opname

let debugVars_term = << debugVars{ 'debugVarItem_list } >>
let debugVars_opname = opname_of_term debugVars_term
let is_debugVars_term = is_dep0_term debugVars_opname
let mk_debugVars_term = mk_dep0_term debugVars_opname
let dest_debugVars_term = dest_dep0_term debugVars_opname

let debugString_term = << debugString{ 'string } >>
let debugString_opname = opname_of_term debugString_term
let is_debugString_term = is_dep0_term debugString_opname
let mk_debugString_term = mk_dep0_term debugString_opname
let dest_debugString_term = dest_dep0_term debugString_opname

let debugContext_term = << debugContext{ 'debug_line; 'debug_vars } >>
let debugContext_opname = opname_of_term debugContext_term
let is_debugContext_term = is_dep0_dep0_term debugContext_opname
let mk_debugContext_term = mk_dep0_dep0_term debugContext_opname
let dest_debugContext_term = dest_dep0_dep0_term debugContext_opname

(*
 * Expressions.
 *)

(* Primitive operations. *)

let letUnop_term = << letUnop{ 'ty; 'unop; 'atom; var. 'exp['var] } >>
let letUnop_opname = opname_of_term letUnop_term
let is_letUnop_term = is_3_dep0_1_dep1_term letUnop_opname
let mk_letUnop_term = mk_3_dep0_1_dep1_term letUnop_opname
let dest_letUnop_term = dest_3_dep0_1_dep1_term letUnop_opname

let letBinop_term =
   << letBinop{ 'ty; 'binop; 'atom1; 'atom2; var. 'exp['var] } >>
let letBinop_opname = opname_of_term letBinop_term
let is_letBinop_term = is_4_dep0_1_dep1_term letBinop_opname
let mk_letBinop_term = mk_4_dep0_1_dep1_term letBinop_opname
let dest_letBinop_term = dest_4_dep0_1_dep1_term letBinop_opname

(* Function application. *)

let letExt_term =
   << letExt{ 'ty1; 'string; 'ty2; 'atom_list; var. 'exp['var] } >>
let letExt_opname = opname_of_term letExt_term
let is_letExt_term = is_4_dep0_1_dep1_term letExt_opname
let mk_letExt_term = mk_4_dep0_1_dep1_term letExt_opname
let dest_letExt_term = dest_4_dep0_1_dep1_term letExt_opname

let tailCall_term = << tailCall{ 'label; 'var; 'atom_list } >>
let tailCall_opname = opname_of_term tailCall_term
let is_tailCall_term = is_dep0_dep0_dep0_term tailCall_opname
let mk_tailCall_term = mk_dep0_dep0_dep0_term tailCall_opname
let dest_tailCall_term = dest_dep0_dep0_dep0_term tailCall_opname

let specialCall_term = << specialCall{ 'label; 'tailop } >>
let specialCall_opname = opname_of_term specialCall_term
let is_specialCall_term = is_dep0_dep0_term specialCall_opname
let mk_specialCall_term = mk_dep0_dep0_term specialCall_opname
let dest_specialCall_term = dest_dep0_dep0_term specialCall_opname

(* Control. *)

let matchCase_term = << matchCase{ 'label; 'set; 'exp } >>
let matchCase_opname = opname_of_term matchCase_term
let is_matchCase_term = is_dep0_dep0_dep0_term matchCase_opname
let mk_matchCase_term = mk_dep0_dep0_dep0_term matchCase_opname
let dest_matchCase_term = dest_dep0_dep0_dep0_term matchCase_opname

let matchExp_term = << matchExp{ 'atom; 'matchCase_list } >>
let matchExp_opname = opname_of_term matchExp_term
let is_matchExp_term = is_dep0_dep0_term matchExp_opname
let mk_matchExp_term = mk_dep0_dep0_term matchExp_opname
let dest_matchExp_term = dest_dep0_dep0_term matchExp_opname

let typeCase_term =
   << typeCase{ 'atom1; 'atom2; 'var1; 'var2; 'exp1; 'exp2 } >>
let typeCase_opname = opname_of_term typeCase_term
let is_typeCase_term = is_6_dep0_term typeCase_opname
let mk_typeCase_term = mk_6_dep0_term typeCase_opname
let dest_typeCase_term = dest_6_dep0_term typeCase_opname

(* Allocation. *)

let letAlloc_term = << letAlloc{ 'alloc_op; var. 'exp['var] } >>
let letAlloc_opname = opname_of_term letAlloc_term
let is_letAlloc_term = is_dep0_dep1_term letAlloc_opname
let mk_letAlloc_term = mk_dep0_dep1_term letAlloc_opname
let dest_letAlloc_term = dest_dep0_dep1_term letAlloc_opname

(* Subscripting *)

let letSubscript_term =
   << letSubscript{ 'subop; 'ty; 'var2; 'atom; var1. 'exp['var1] } >>
let letSubscript_opname = opname_of_term letSubscript_term
let is_letSubscript_term = is_4_dep0_1_dep1_term letSubscript_opname
let mk_letSubscript_term = mk_4_dep0_1_dep1_term letSubscript_opname
let dest_letSubscript_term = dest_4_dep0_1_dep1_term letSubscript_opname

let setSubscript_term =
   << setSubscript{ 'subop; 'label; 'var; 'atom1; 'ty; 'atom2; 'exp } >>
let setSubscript_opname = opname_of_term setSubscript_term
let is_setSubscript_term = is_7_dep0_term setSubscript_opname
let mk_setSubscript_term = mk_7_dep0_term setSubscript_opname
let dest_setSubscript_term = dest_7_dep0_term setSubscript_opname

let setGlobal_term =
   << setGlobal{ 'sub_value; 'label; 'var; 'ty; 'atom; 'exp } >>
let setGlobal_opname = opname_of_term setGlobal_term
let is_setGlobal_term = is_6_dep0_term setGlobal_opname
let mk_setGlobal_term = mk_6_dep0_term setGlobal_opname
let dest_setGlobal_term = dest_6_dep0_term setGlobal_opname

let memcpy_term =
   << memcpy{ 'subop; 'label; 'var1; 'atom1; 'var2; 'atom2; 'atom3; 'exp } >>
let memcpy_opname = opname_of_term memcpy_term
let is_memcpy_term = is_8_dep0_term memcpy_opname
let mk_memcpy_term = mk_8_dep0_term memcpy_opname
let dest_memcpy_term = dest_8_dep0_term memcpy_opname

(* Assertions. *)

let call_term = << call{ 'label; 'var; 'atom_option_list; 'exp } >>
let call_opname = opname_of_term call_term
let is_call_term = is_4_dep0_term call_opname
let mk_call_term = mk_4_dep0_term call_opname
let dest_call_term = dest_4_dep0_term call_opname

let assertExp_term = << assertExp{ 'label; 'pred; 'exp } >>
let assertExp_opname = opname_of_term assertExp_term
let is_assertExp_term = is_dep0_dep0_dep0_term assertExp_opname
let mk_assertExp_term = mk_dep0_dep0_dep0_term assertExp_opname
let dest_assertExp_term = dest_dep0_dep0_dep0_term assertExp_opname

(* Debugging. *)

let debug_term = << debug{ 'debug_info; 'exp } >>
let debug_opname = opname_of_term debug_term
let is_debug_term = is_dep0_dep0_term debug_opname
let mk_debug_term = mk_dep0_dep0_term debug_opname
let dest_debug_term = dest_dep0_dep0_term debug_opname

(*
 * Function definition.
 *)

let fundef_term = << fundef{ 'debug_line; 'ty; 'var_list; 'exp } >>
let fundef_opname = opname_of_term fundef_term
let is_fundef_term = is_4_dep0_term fundef_opname
let mk_fundef_term = mk_4_dep0_term fundef_opname
let dest_fundef_term = dest_4_dep0_term fundef_opname
