(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define and implement the basic expression forms in the FIR.
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

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Unary operations.
 *)

(* Identity (polymorphic). *)
declare idOp

(* Naml ints. *)
declare uminusIntOp
declare notIntOp

(* Bit fields. *)
declare rawBitFieldOp{ 'precision; 'sign; 'num1; 'num2 }

(* Native ints. *)
declare uminusRawIntOp{ 'precision; 'sign }
declare notRawIntOp{ 'precision; 'sign }

(* Floats. *)
declare uminusFloatOp{ 'precision }
declare absFloatOp{ 'precision }
declare sinOp{ 'precision }
declare cosOp{ 'precision }
declare sqrtOp{ 'precision }

(* Coerce to int. *)
declare intOfFloatOp{ 'precision }

(* Coerce to float. *)
declare floatOfIntOp{ 'precision }
declare floatOfFloatOp{ 'prec1; 'prec2 }
declare floatOfRawIntOp{ 'float_prec; 'int_prec; 'int_sign }

(* Coerce to rawint. *)
declare rawIntOfEnumOp{ 'precision; 'sign; 'num }
declare rawIntOfFloatOp{ 'int_prec; 'int_sign; 'float_prec }
declare rawIntOfRawIntOp{ 'dest_prec; 'dest_sign; 'src_prec; 'src_sign }

(* Integer/pointer coercions. *)
declare rawIntOfPointerOp{ 'precision; 'sign }
declare pointerOfRawIntOp{ 'precision; 'sign }

(*
 * Binary operations.
 *)

(* Enums. *)
declare andEnumOp{ 'num }
declare orEnumOp{ 'num }

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
declare plusRawIntOp{ 'precision; 'sign }
declare minusRawIntOp{ 'precision; 'sign }
declare mulRawIntOp{ 'precision; 'sign }
declare divRawIntOp{ 'precision; 'sign }
declare remRawIntOp{ 'precision; 'sign }
declare slRawIntOp{ 'precision; 'sign }
declare srRawIntOp{ 'precision; 'sign }
declare andRawIntOp{ 'precision; 'sign }
declare orRawIntOp{ 'precision; 'sign }
declare xorRawIntOp{ 'precision; 'sign }
declare maxRawIntOp{ 'precision; 'sign }
declare minRawIntOp{ 'precision; 'sign }

declare rawSetBitFieldOp{ 'precision; 'sign; 'num1; 'num2 }

declare eqRawIntOp{ 'precision; 'sign }
declare neqRawIntOp{ 'precision; 'sign }
declare ltRawIntOp{ 'precision; 'sign }
declare leRawIntOp{ 'precision; 'sign }
declare gtRawIntOp{ 'precision; 'sign }
declare geRawIntOp{ 'precision; 'sign }
declare cmpRawIntOp{ 'precision; 'sign }

(* Floats. *)
declare plusFloatOp{ 'precision }
declare minusFloatOp{ 'precision }
declare mulFloatOp{ 'precision }
declare divFloatOp{ 'precision }
declare remFloatOp{ 'precision }
declare maxFloatOp{ 'precision }
declare minFloatOp{ 'precision }

declare eqFloatOp{ 'precision }
declare neqFloatOp{ 'precision }
declare ltFloatOp{ 'precision }
declare leFloatOp{ 'precision }
declare gtFloatOp{ 'precision }
declare geFloatOp{ 'precision }
declare cmpFloatOp{ 'precision }

declare atan2Op{ 'precision }

(* Pointer equality. *)
declare eqEqOp
declare neqEqOp

(*
 * Subscript operators.
 *)
declare blockPolySub
declare blockRawIntSub{ 'precision; 'sign }
declare blockFloatSub{ 'precision }
declare rawRawIntSub{ 'precision; 'sign }
declare rawFloatSub{ 'precision }
declare rawDataSub
declare rawFunctionSub

(*
 * Allocation operators.
 *)
declare allocTuple{ 'ty; 'atom_list }
declare allocArray{ 'ty; 'atom_list }
declare allocUnion{ 'ty; 'ty_var; 'num; 'atom_list }
declare allocMalloc{ 'atom }

(*
 * Normal values.
 *)
declare atomInt{ 'int }
declare atomEnum{ 'bound; 'num }
declare atomRawInt{ 'precision; 'sign; 'num }
declare atomFloat{ 'f }
declare atomConst{ 'ty; 'ty_var; 'num }
declare atomVar{ 'var }

(*
 * Expressions.
 *)

(* Primitive operations. *)
declare letUnop{ 'op; 'ty; 'a1; v. 'exp['v] }
declare letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp['v] }

(* Function application. *)
declare letExt{ 'ty; 'string; 'ty_of_str; 'atom_list; v. 'exp['v] }
declare tailCall{ 'var; 'atom_list }

(* Control. *)
declare matchCase{ 'set; 'exp }
declare "match"{ 'key; 'cases }

(* Allocation. *)
declare letAlloc{ 'alloc_op; v. 'exp['v] }

(* Subscripting. *)
declare letSubscript{ 'subop; 'ty; 'var; 'index; v. 'exp['v] }
declare setSubscript{ 'subop; 'ty; 'var; 'index; 'new_val; v. 'exp['v] }
declare memcpy{ 'subop; 'var1; 'atom1; 'var2; 'atom2; 'len; 'exp }


(*************************************************************************
 * Display forms.
 *************************************************************************)

(*
 * Unary operations.
 *)

(* Identity (polymorphic). *)
dform idOp_df : except_mode[src] :: idOp = `"id"

(* Naml ints. *)
dform uminusIntOp_df : except_mode[src] :: uminusIntOp = `"-"
dform notIntOp_df : except_mode[src] :: notIntOp = `"~"

(* Bit fields. *)
dform rawBitFieldOp_df : except_mode[src] ::
   rawBitFieldOp{ 'precision; 'sign; 'num1; 'num2 } =
   `"RawBitFieldOp(" slot{'precision} `", " slot{'sign} `", "
   slot{'num1} `", " slot{'num2} `")"

(* Native ints. *)
dform uminusRawIntOp_df : except_mode[src] ::
   uminusRawIntOp{ 'precision; 'sign } =
   `"UminusRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform notRawIntOp_df : except_mode[src] ::
   notRawIntOp{ 'precision; 'sign } =
   `"NotRawIntOp(" slot{'precision} `", " slot{'sign} `")"

(* Floats. *)
dform uminusFloatOp_df : except_mode[src] :: uminusFloatOp{ 'precision } =
   `"UminusFloatOp(" slot{'precision} `")"
dform absFloatOp_df : except_mode[src] :: absFloatOp{ 'precision } =
   `"AbsFloatOp(" slot{'precision} `")"
dform sinOp_df : except_mode[src] :: sinOp{ 'precision } =
   `"sinOp(" slot{'precision} `")"
dform cosOp_df : except_mode[src] :: cosOp{ 'precision } =
   `"cosOp(" slot{'precision} `")"
dform sqrtOp_df : except_mode[src] :: sqrtOp{ 'precision } =
   `"sqrtOp(" slot{'precision} `")"

(* Coerce to int. *)
dform intOfFloatOp_df : except_mode[src] :: intOfFloatOp{ 'precision } =
   `"IntOfFloatOp(" slot{'precision} `")"

(* Coerce to float. *)
dform floatOfIntOp_df : except_mode[src] ::
   floatOfIntOp{ 'precision } =
   `"FloatOfIntOp(" slot{'precision} `")"
dform floatOfFLoatOp_df : except_mode[src] ::
   floatOfFloatOp{ 'prec1; 'prec2 } =
   `"FloatOfFloatOp(" slot{'prec1} `", " slot{'prec2} `")"
dform floatOfRawIntOp_df : except_mode[src] ::
   floatOfRawIntOp{ 'float_prec; 'int_prec; 'int_sign } =
   `"FloatOfRawIntOp(" slot{'float_prec} `", " slot{'int_prec}
   `", " slot{'int_sign} `")"

(* Coerce to rawint. *)
dform rawIntOfEnumOp_df : except_mode[src] ::
   rawIntOfEnumOp{ 'precision; 'sign; 'num } =
   `"RawIntOfEnumOp(" slot{'precision} `", " slot{'sign}
   `", " slot{'num} `")"
dform rawIntOfFloatOp_df : except_mode[src] ::
   rawIntOfFloatOp{ 'int_prec; 'int_sign; 'float_prec } =
   `"RawIntOfFloatOp(" slot{'int_prec} `", " slot{'int_sign}
   `", " slot{'float_prec} `")"
dform rawIntOfRawIntOp_df : except_mode[src] ::
   rawIntOfRawIntOp{ 'dest_prec; 'dest_sign; 'src_prec; 'src_sign } =
   `"RawIntOfRawIntOp(" slot{'dest_prec} `", " slot{'dest_sign}
   `", " slot{'src_prec} `", " slot{'src_sign} `")"

(* Integer/pointer coercions. *)
dform rawIntOfPointerOp_df : except_mode[src] ::
   rawIntOfPointerOp{ 'precision; 'sign } =
   `"RawIntOfPointerOp(" slot{'precision} `", " slot{'sign} `")"
dform pointerOfRawIntOp_df : except_mode[src] ::
   pointerOfRawIntOp{ 'precision; 'sign } =
   `"PointerOfRawIntOp(" slot{'precision} `", " slot{'sign} `")"

(*
 * Binary operations.
 *)

(* Enums. *)
dform andEnumOp_df : except_mode[src] :: andEnumOp{ 'num } =
   `"AndEnumOp(" slot{'num} `")"
dform orEnumOp_df : except_mode[src] :: orEnumOp{ 'num } =
   `"OrEnumOp(" slot{'num} `")"

(* Naml ints. *)
dform plusIntOp_df : except_mode[src] :: plusIntOp = `"+"
dform minusIntOp_df : except_mode[src] :: minusIntOp = `"-"
dform mulIntOp_df : except_mode[src] :: mulIntOp = `"*"
dform divIntOp_df : except_mode[src] :: divIntOp = Nuprl_font!"div"
dform remIntOp_df : except_mode[src] :: remIntOp = `"rem"
dform lslIntOp_df : except_mode[src] :: lslIntOp = `"<<"
dform lsrIntOp_df : except_mode[src] :: lsrIntOp = `">>"
dform asrIntOp_df : except_mode[src] :: asrIntOp = `">>"
dform andIntOp_df : except_mode[src] :: andIntOp = `"&"
dform orIntOp_df  : except_mode[src] :: orIntOp  = `"|"
dform xorIntOp_df : except_mode[src] :: xorIntOp = `"^"
dform maxIntOp_df : except_mode[src] :: maxIntOp = `"max"
dform minIntOp_df : except_mode[src] :: minIntOp = `"min"

dform eqIntOp_df : except_mode[src] :: eqIntOp = `"="
dform neqIntOp_df : except_mode[src] :: neqIntOp = `"!="
dform ltIntOp_df : except_mode[src] :: ltIntOp = `"<"
dform leIntOp_df : except_mode[src] :: leIntOp = Nuprl_font!le
dform gtIntOp_df : except_mode[src] :: gtIntOp = `">"
dform geIntOp_df : except_mode[src] :: geIntOp = Nuprl_font!ge
dform cmpIntOp_df : except_mode[src] :: cmpIntOp = `"cmp"

(* Native ints. *)
dform plusRawIntOp_df : except_mode[src] ::
   plusRawIntOp{ 'precision; 'sign } =
   `"PlusRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform minusRawIntOp_df : except_mode[src] ::
   minusRawIntOp{ 'precision; 'sign } =
   `"MinusRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform mulRawIntOp_df : except_mode[src] ::
   mulRawIntOp{ 'precision; 'sign } =
   `"MulRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform divRawIntOp_df : except_mode[src] ::
   divRawIntOp{ 'precision; 'sign } =
   `"DivRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform remRawIntOp_df : except_mode[src] ::
   remRawIntOp{ 'precision; 'sign } =
   `"RemRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform slRawIntOp_df : except_mode[src] ::
   slRawIntOp{ 'precision; 'sign } =
   `"SlRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform srRawIntOp_df : except_mode[src] ::
   srRawIntOp{ 'precision; 'sign } =
   `"SrRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform andRawIntOp_df : except_mode[src] ::
   andRawIntOp{ 'precision; 'sign } =
   `"AndRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform orRawIntOp_df : except_mode[src] ::
   orRawIntOp{ 'precision; 'sign } =
   `"OrRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform xorRawIntOp_df : except_mode[src] ::
   xorRawIntOp{ 'precision; 'sign } =
   `"XorRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform maxRawIntOp_df : except_mode[src] ::
   maxRawIntOp{ 'precision; 'sign } =
   `"MaxRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform minRawIntOp_df : except_mode[src] ::
   minRawIntOp{ 'precision; 'sign } =
   `"MinRawIntOp(" slot{'precision} `", " slot{'sign} `")"

dform rawSetBitFieldOp_df : except_mode[src] ::
   rawSetBitFieldOp{ 'precision; 'sign; 'num1; 'num2 } =
   `"RawSetBitFieldOp(" slot{'precision} `", " slot{'sign}
   `", " slot{'num1} `", " slot{'num2} `")"

dform eqRawIntOp_df : except_mode[src] ::
   eqRawIntOp{ 'precision; 'sign } =
   `"EqRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform neqRawIntOp_df : except_mode[src] ::
   neqRawIntOp{ 'precision; 'sign } =
   `"NeqRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform ltRawIntOp_df : except_mode[src] ::
   ltRawIntOp{ 'precision; 'sign } =
   `"LtRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform leRawIntOp_df : except_mode[src] ::
   leRawIntOp{ 'precision; 'sign } =
   `"LeRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform gtRawIntOp_df : except_mode[src] ::
   gtRawIntOp{ 'precision; 'sign } =
   `"GtRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform geRawIntOp_df : except_mode[src] ::
   geRawIntOp{ 'precision; 'sign } =
   `"GeRawIntOp(" slot{'precision} `", " slot{'sign} `")"
dform cmpRawIntOp_df : except_mode[src] ::
   cmpRawIntOp{ 'precision; 'sign } =
   `"CmpRawIntOp(" slot{'precision} `", " slot{'sign} `")"

(* Floats. *)
dform plusFloatOp_df : except_mode[src] :: plusFloatOp{ 'precision } =
   `"PlusFloatOp(" slot{'precision} `")"
dform minusFloatOp_df : except_mode[src] :: minusFloatOp{ 'precision } =
   `"MinusFloatOp(" slot{'precision} `")"
dform mulFloatOp_df : except_mode[src] :: mulFloatOp{ 'precision } =
   `"MulFloatOp(" slot{'precision} `")"
dform divFloatOp_df : except_mode[src] :: divFloatOp{ 'precision } =
   `"DivFloatOp(" slot{'precision} `")"
dform remFloatOp_df : except_mode[src] :: remFloatOp{ 'precision } =
   `"RemFloatOp(" slot{'precision} `")"
dform maxFloatOp_df : except_mode[src] :: maxFloatOp{ 'precision } =
   `"MaxFloatOp(" slot{'precision} `")"
dform minFloatOp_df : except_mode[src] :: minFloatOp{ 'precision } =
   `"MinFloatOp(" slot{'precision} `")"

dform eqFloatOp_df : except_mode[src] :: eqFloatOp{ 'precision } =
   `"EqFloatOp(" slot{'precision} `")"
dform neqFloatOp_df : except_mode[src] :: neqFloatOp{ 'precision } =
   `"NeqFloatOp(" slot{'precision} `")"
dform ltFloatOp_df : except_mode[src] :: ltFloatOp{ 'precision } =
   `"LtFloatOp(" slot{'precision} `")"
dform leFloatOp_df : except_mode[src] :: leFloatOp{ 'precision } =
   `"LeFloatOp(" slot{'precision} `")"
dform gtFloatOp_df : except_mode[src] :: gtFloatOp{ 'precision } =
   `"GtFloatOp(" slot{'precision} `")"
dform geFloatOp_df : except_mode[src] :: geFloatOp{ 'precision } =
   `"GeFloatOp(" slot{'precision} `")"
dform cmpFloatOp_df : except_mode[src] :: cmpFloatOp{ 'precision } =
   `"CmpFloatOp(" slot{'precision} `")"

dform atan2Op_df : except_mode[src] :: atan2Op{ 'precision } =
   `"atan2Op(" slot{'precision} `")"

(* Pointer equality. *)
dform eqEqOp_df : except_mode[src] :: eqEqOp = `"EqEqOp"
dform neqEqOp_df : except_mode[src] :: neqEqOp = `"NeqEqOp"

(*
 * Subscript operators.
 *)
dform blockPolySub_df : except_mode[src] :: blockPolySub =
   `"BlockPolySub"
dform blockRawIntSub_df : except_mode[src] :: blockRawIntSub{ 'p; 's } =
   `"BlockRawIntSub(" slot{'p} `", " slot{'s} `")"
dform blockFloatSub_df : except_mode[src] :: blockFloatSub{ 'precision } =
   `"BlockFloatSub(" slot{'precision} `")"
dform rawRawIntSub_df : except_mode[src] :: rawRawIntSub{ 'p; 's } =
   `"RawRawIntSub(" slot{'p} `", " slot{'s} `")"
dform rawFloatSub_df : except_mode[src] :: rawFloatSub{ 'precision } =
   `"RawFloatSub(" slot{'precision} `")"
dform rawDataSub_df : except_mode[src] :: rawDataSub =
   `"RawDataSub"
dform rawFunctionSub : except_mode[src] :: rawFunctionSub =
   `"RawFunctionSub"

(*
 * Allocation operators.
 *)
dform allocTuple_df : except_mode[src] :: allocTuple{ 'ty; 'atom_list } =
   szone `"AllocTuple(" slot{'ty} `", " slot{'atom_list} `")" ezone
dform allocArray_df : except_mode[src] :: allocArray{ 'ty; 'atom_list } =
   szone `"AllocArray(" slot{'ty} `", " slot{'atom_list} `")" ezone
dform allocUnion_df : except_mode[src] ::
   allocUnion{ 'ty; 'ty_var; 'num; 'atom_list } =
   szone `"AllocUnion(" slot{'ty} `", " slot{'ty_var} `", "
   slot{'num} `", " slot{'atom_list } `")" ezone
dform allocMalloc_df : except_mode[src] :: allocMalloc{ 'atom } =
   `"AllocMalloc(" slot{'atom} `")"

(*
 * Normal values.
 *)
dform atomInt_df : except_mode[src] :: atomInt{ 'int } =
   lzone `"AtomInt(" slot{'int} `")" ezone
dform atomEnum_df : except_mode[src] :: atomEnum{ 'bound; 'num } =
   lzone `"AtomEnum(" slot{'bound} `", " slot{'num} `")" ezone
dform atomRawInt_df : except_mode[src] ::
   atomRawInt{ 'precision; 'sign; 'num } =
   lzone `"AtomRawInt(" slot{'precision} `", "
   slot{'sign} `", " slot{'num} `")" ezone
dform atomFloat_df : except_mode[src] :: atomFloat{ 'f } =
   lzone `"AtomFloat(" slot{'f} `")" ezone
dform atomConst_df : except_mode[src] :: atomConst{ 'ty; 'ty_var; 'num } =
   lzone `"AtomConst(" slot{'ty} `", " slot{'ty_var} `", "
   slot{'num} `")" ezone
dform atomVar_df : except_mode[src] :: atomVar{ 'var } =
   szone `"AtomVar(" slot{'var} `")" ezone

(*
 * Expressions.
 *)

(* Primitive operations. *)
dform letUnop_df : except_mode[src] ::
   letUnop{ 'op; 'ty; 'a1; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `":" slot{'ty} `" =" hspace
   lzone slot{'op} `"(" slot{'a1} `")" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform letBinop_df : except_mode[src] ::
   letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `":" slot{'ty} `" =" hspace
   lzone `"(" slot{'a1} `" " slot{'op} `" " slot{'a2} `")" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm

(* Function application. *)
dform letExt_df : except_mode[src] ::
   letExt{ 'ty; 'string; 'ty_of_str; 'atom_list; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `":" slot{'ty} `" =" hspace
   szone slot{'string} `":" slot{'ty_of_str}
   `"(" slot{'atom_list} `")" ezone popm
   ezone popm
dform tailCall_df : except_mode[src] :: tailCall{ 'var; 'atom_list } =
   szone `"TailCall(" slot{'var} `", " slot{'atom_list} `")" ezone

(* Control. *)
dform matchCase_df : except_mode[src] :: matchCase{ 'set; 'exp } =
   pushm[0] szone push_indent slot{'set} `" ->" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform match_df : except_mode[src] :: "match"{ 'key; 'cases } =
   pushm[0] szone push_indent `"match" hspace
   szone slot{'key} ezone popm hspace
   push_indent `"in" hspace
   szone slot{'cases} ezone popm
   ezone popm

(* Allocation. *)
dform letAlloc_df : except_mode[src] ::
   letAlloc{ 'alloc_op; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone slot{'alloc_op} ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm

(* Subscripting. *)
dform letSubscript_df : except_mode[src] ::
   letSubscript{ 'subop; 'ty; 'ref; 'index; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `":" slot{'ty} `" =" hspace
   lzone slot{'ref} `"[" slot{'index} `"]" ezone popm hspace
   `"with subop " slot{'subop} hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform setSubscript_df : except_mode[src] ::
   setSubscript{ 'subop; 'ty; 'ref; 'index; 'new_val; v. 'exp } =
   szone slot{'ref} `"[" slot{'index} `"]" Nuprl_font!leftarrow
   slot{'new_val} hspace
   `"with subop " slot{'subop} hspace
   slot{'exp} ezone
dform memcpy_df : except_mode[src] ::
   memcpy{ 'subop; 'var1; 'atom1; 'var2; 'atom2; 'len; 'exp } =
   szone `"memcpy(" slot{'var1} `"[" slot{'atom1} `"], "
   slot{'var2} `"[" slot{'atom2} `"], " slot{'len} `")" hspace
   `"with subop " slot{'subop} hspace
   slot{'exp} ezone

(*************************************************************************
 * Term operations.
 *************************************************************************)

(*******************
 * Unary operations.
 *******************)

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

(*
let rawBitFieldOp_term = << rawBitFieldOp{ 'precision; 'sign; 'num1; 'num2 } >>
let rawBitFieldOp_opname = opname_of_term rawBitFieldOp_term
let is_rawBitFieldOp_term = is_dep0_dep0_dep0_dep0_term rawBitFieldOp_opname
let mk_rawBitFieldOp_term = mk_dep0_dep0_dep0_dep0_term rawBitFieldOp_opname
let dest_rawBitFieldOp_term =
   dest_dep0_dep0_dep0_dep0_term rawBitFieldOp_opname
*)

(* Native ints. *)

let uminusRawIntOp_term = << uminusRawIntOp{ 'precision; 'sign } >>
let uminusRawIntOp_opname = opname_of_term uminusRawIntOp_term
let is_uminusRawIntOp_term = is_dep0_dep0_term uminusRawIntOp_opname
let mk_uminusRawIntOp_term = mk_dep0_dep0_term uminusRawIntOp_opname
let dest_uminusRawIntOp_term = dest_dep0_dep0_term uminusRawIntOp_opname

let notRawIntOp_term = << notRawIntOp{ 'precision; 'sign } >>
let notRawIntOp_opname = opname_of_term notRawIntOp_term
let is_notRawIntOp_term = is_dep0_dep0_term notRawIntOp_opname
let mk_notRawIntOp_term = mk_dep0_dep0_term notRawIntOp_opname
let dest_notRawIntOp_term = dest_dep0_dep0_term notRawIntOp_opname

(* Floats. *)

let uminusFloatOp_term = << uminusFloatOp{ 'precision } >>
let uminusFloatOp_opname = opname_of_term uminusFloatOp_term
let is_uminusFloatOp_term = is_dep0_term uminusFloatOp_opname
let mk_uminusFloatOp_term = mk_dep0_term uminusFloatOp_opname
let dest_uminusFloatOp_term = dest_dep0_term uminusFloatOp_opname

let absFloatOp_term = << absFloatOp{ 'precision } >>
let absFloatOp_opname = opname_of_term absFloatOp_term
let is_absFloatOp_term = is_dep0_term absFloatOp_opname
let mk_absFloatOp_term = mk_dep0_term absFloatOp_opname
let dest_absFloatOp_term = dest_dep0_term absFloatOp_opname

let sinOp_term = << sinOp{ 'precision } >>
let sinOp_opname = opname_of_term sinOp_term
let is_sinOp_term = is_dep0_term sinOp_opname
let mk_sinOp_term = mk_dep0_term sinOp_opname
let dest_sinOp_term = dest_dep0_term sinOp_opname

let cosOp_term = << cosOp{ 'precision } >>
let cosOp_opname = opname_of_term cosOp_term
let is_cosOp_term = is_dep0_term cosOp_opname
let mk_cosOp_term = mk_dep0_term cosOp_opname
let dest_cosOp_term = dest_dep0_term cosOp_opname

let sqrtOp_term = << sqrtOp{ 'precision } >>
let sqrtOp_opname = opname_of_term sqrtOp_term
let is_sqrtOp_term = is_dep0_term sqrtOp_opname
let mk_sqrtOp_term = mk_dep0_term sqrtOp_opname
let dest_sqrtOp_term = dest_dep0_term sqrtOp_opname

(* Coerce to int. *)

let intOfFloatOp_term = << intOfFloatOp{ 'precision } >>
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

let rawIntOfEnumOp_term = << rawIntOfEnumOp{ 'precision; 'sign; 'num } >>
let rawIntOfEnumOp_opname = opname_of_term rawIntOfEnumOp_term
let is_rawIntOfEnumOp_term = is_dep0_dep0_dep0_term rawIntOfEnumOp_opname
let mk_rawIntOfEnumOp_term = mk_dep0_dep0_dep0_term rawIntOfEnumOp_opname
let dest_rawIntOfEnumOp_term = dest_dep0_dep0_dep0_term rawIntOfEnumOp_opname

let rawIntOfFloatOp_term =
   << rawIntOfFloatOp{ 'int_prec; 'int_sign; 'float_prec } >>
let rawIntOfFloatOp_opname = opname_of_term rawIntOfFloatOp_term
let is_rawIntOfFloatOp_term = is_dep0_dep0_dep0_term rawIntOfFloatOp_opname
let mk_rawIntOfFloatOp_term = mk_dep0_dep0_dep0_term rawIntOfFloatOp_opname
let dest_rawIntOfFloatOp_term = dest_dep0_dep0_dep0_term rawIntOfFloatOp_opname

let rawIntOfRawIntOp_term =
   << rawIntOfRawIntOp{ 'dest_prec; 'dest_sign; 'src_prec; 'src_sign } >>
let rawIntOfRawIntOp_opname = opname_of_term rawIntOfRawIntOp_term
let is_rawIntOfRawIntOp_term = is_dep0_dep0_dep0_term rawIntOfRawIntOp_opname
let mk_rawIntOfRawIntOp_term = mk_dep0_dep0_dep0_term rawIntOfRawIntOp_opname
let dest_rawIntOfRawIntOp_term =
   dest_dep0_dep0_dep0_term rawIntOfRawIntOp_opname

(* Integer/pointer coercions. *)

let rawIntOfPointerOp_term = << rawIntOfPointerOp{ 'precision; 'sign } >>
let rawIntOfPointerOp_opname = opname_of_term rawIntOfPointerOp_term
let is_rawIntOfPointerOp_term = is_dep0_dep0_term rawIntOfPointerOp_opname
let mk_rawIntOfPointerOp_term = mk_dep0_dep0_term rawIntOfPointerOp_opname
let dest_rawIntOfPointerOp_term = dest_dep0_dep0_term rawIntOfPointerOp_opname

let pointerOfRawIntOp_term = << pointerOfRawIntOp{ 'precision; 'sign } >>
let pointerOfRawIntOp_opname = opname_of_term pointerOfRawIntOp_term
let is_pointerOfRawIntOp_term = is_dep0_dep0_term pointerOfRawIntOp_opname
let mk_pointerOfRawIntOp_term = mk_dep0_dep0_term pointerOfRawIntOp_opname
let dest_pointerOfRawIntOp_term = dest_dep0_dep0_term pointerOfRawIntOp_opname

(********************
 * Binary operations.
 ********************)

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

let plusRawIntOp_term = << plusRawIntOp{ 'precision; 'sign } >>
let plusRawIntOp_opname = opname_of_term plusRawIntOp_term
let is_plusRawIntOp_term = is_dep0_dep0_term plusRawIntOp_opname
let mk_plusRawIntOp_term = mk_dep0_dep0_term plusRawIntOp_opname
let dest_plusRawIntOp_term = dest_dep0_dep0_term plusRawIntOp_opname

let minusRawIntOp_term = << minusRawIntOp{ 'precision; 'sign } >>
let minusRawIntOp_opname = opname_of_term minusRawIntOp_term
let is_minusRawIntOp_term = is_dep0_dep0_term minusRawIntOp_opname
let mk_minusRawIntOp_term = mk_dep0_dep0_term minusRawIntOp_opname
let dest_minusRawIntOp_term = dest_dep0_dep0_term minusRawIntOp_opname

let mulRawIntOp_term = << mulRawIntOp{ 'precision; 'sign } >>
let mulRawIntOp_opname = opname_of_term mulRawIntOp_term
let is_mulRawIntOp_term = is_dep0_dep0_term mulRawIntOp_opname
let mk_mulRawIntOp_term = mk_dep0_dep0_term mulRawIntOp_opname
let dest_mulRawIntOp_term = dest_dep0_dep0_term mulRawIntOp_opname

let divRawIntOp_term = << divRawIntOp{ 'precision; 'sign } >>
let divRawIntOp_opname = opname_of_term divRawIntOp_term
let is_divRawIntOp_term = is_dep0_dep0_term divRawIntOp_opname
let mk_divRawIntOp_term = mk_dep0_dep0_term divRawIntOp_opname
let dest_divRawIntOp_term = dest_dep0_dep0_term divRawIntOp_opname

let remRawIntOp_term = << remRawIntOp{ 'precision; 'sign } >>
let remRawIntOp_opname = opname_of_term remRawIntOp_term
let is_remRawIntOp_term = is_dep0_dep0_term remRawIntOp_opname
let mk_remRawIntOp_term = mk_dep0_dep0_term remRawIntOp_opname
let dest_remRawIntOp_term = dest_dep0_dep0_term remRawIntOp_opname

let slRawIntOp_term = << slRawIntOp{ 'precision; 'sign } >>
let slRawIntOp_opname = opname_of_term slRawIntOp_term
let is_slRawIntOp_term = is_dep0_dep0_term slRawIntOp_opname
let mk_slRawIntOp_term = mk_dep0_dep0_term slRawIntOp_opname
let dest_slRawIntOp_term = dest_dep0_dep0_term slRawIntOp_opname

let srRawIntOp_term = << srRawIntOp{ 'precision; 'sign } >>
let srRawIntOp_opname = opname_of_term srRawIntOp_term
let is_srRawIntOp_term = is_dep0_dep0_term srRawIntOp_opname
let mk_srRawIntOp_term = mk_dep0_dep0_term srRawIntOp_opname
let dest_srRawIntOp_term = dest_dep0_dep0_term srRawIntOp_opname

let andRawIntOp_term = << andRawIntOp{ 'precision; 'sign } >>
let andRawIntOp_opname = opname_of_term andRawIntOp_term
let is_andRawIntOp_term = is_dep0_dep0_term andRawIntOp_opname
let mk_andRawIntOp_term = mk_dep0_dep0_term andRawIntOp_opname
let dest_andRawIntOp_term = dest_dep0_dep0_term andRawIntOp_opname

let orRawIntOp_term = << orRawIntOp{ 'precision; 'sign } >>
let orRawIntOp_opname = opname_of_term orRawIntOp_term
let is_orRawIntOp_term = is_dep0_dep0_term orRawIntOp_opname
let mk_orRawIntOp_term = mk_dep0_dep0_term orRawIntOp_opname
let dest_orRawIntOp_term = dest_dep0_dep0_term orRawIntOp_opname

let xorRawIntOp_term = << xorRawIntOp{ 'precision; 'sign } >>
let xorRawIntOp_opname = opname_of_term xorRawIntOp_term
let is_xorRawIntOp_term = is_dep0_dep0_term xorRawIntOp_opname
let mk_xorRawIntOp_term = mk_dep0_dep0_term xorRawIntOp_opname
let dest_xorRawIntOp_term = dest_dep0_dep0_term xorRawIntOp_opname

let maxRawIntOp_term = << maxRawIntOp{ 'precision; 'sign } >>
let maxRawIntOp_opname = opname_of_term maxRawIntOp_term
let is_maxRawIntOp_term = is_dep0_dep0_term maxRawIntOp_opname
let mk_maxRawIntOp_term = mk_dep0_dep0_term maxRawIntOp_opname
let dest_maxRawIntOp_term = dest_dep0_dep0_term maxRawIntOp_opname

let minRawIntOp_term = << minRawIntOp{ 'precision; 'sign } >>
let minRawIntOp_opname = opname_of_term minRawIntOp_term
let is_minRawIntOp_term = is_dep0_dep0_term minRawIntOp_opname
let mk_minRawIntOp_term = mk_dep0_dep0_term minRawIntOp_opname
let dest_minRawIntOp_term = dest_dep0_dep0_term minRawIntOp_opname

(* raw set bit field op goes here *)

let eqRawIntOp_term = << eqRawIntOp{ 'precision; 'sign } >>
let eqRawIntOp_opname = opname_of_term eqRawIntOp_term
let is_eqRawIntOp_term = is_dep0_dep0_term eqRawIntOp_opname
let mk_eqRawIntOp_term = mk_dep0_dep0_term eqRawIntOp_opname
let dest_eqRawIntOp_term = dest_dep0_dep0_term eqRawIntOp_opname

let neqRawIntOp_term = << neqRawIntOp{ 'precision; 'sign } >>
let neqRawIntOp_opname = opname_of_term neqRawIntOp_term
let is_neqRawIntOp_term = is_dep0_dep0_term neqRawIntOp_opname
let mk_neqRawIntOp_term = mk_dep0_dep0_term neqRawIntOp_opname
let dest_neqRawIntOp_term = dest_dep0_dep0_term neqRawIntOp_opname

let ltRawIntOp_term = << ltRawIntOp{ 'precision; 'sign } >>
let ltRawIntOp_opname = opname_of_term ltRawIntOp_term
let is_ltRawIntOp_term = is_dep0_dep0_term ltRawIntOp_opname
let mk_ltRawIntOp_term = mk_dep0_dep0_term ltRawIntOp_opname
let dest_ltRawIntOp_term = dest_dep0_dep0_term ltRawIntOp_opname

let leRawIntOp_term = << leRawIntOp{ 'precision; 'sign } >>
let leRawIntOp_opname = opname_of_term leRawIntOp_term
let is_leRawIntOp_term = is_dep0_dep0_term leRawIntOp_opname
let mk_leRawIntOp_term = mk_dep0_dep0_term leRawIntOp_opname
let dest_leRawIntOp_term = dest_dep0_dep0_term leRawIntOp_opname

let gtRawIntOp_term = << gtRawIntOp{ 'precision; 'sign } >>
let gtRawIntOp_opname = opname_of_term gtRawIntOp_term
let is_gtRawIntOp_term = is_dep0_dep0_term gtRawIntOp_opname
let mk_gtRawIntOp_term = mk_dep0_dep0_term gtRawIntOp_opname
let dest_gtRawIntOp_term = dest_dep0_dep0_term gtRawIntOp_opname

let geRawIntOp_term = << geRawIntOp{ 'precision; 'sign } >>
let geRawIntOp_opname = opname_of_term geRawIntOp_term
let is_geRawIntOp_term = is_dep0_dep0_term geRawIntOp_opname
let mk_geRawIntOp_term = mk_dep0_dep0_term geRawIntOp_opname
let dest_geRawIntOp_term = dest_dep0_dep0_term geRawIntOp_opname

let cmpRawIntOp_term = << cmpRawIntOp{ 'precision; 'sign } >>
let cmpRawIntOp_opname = opname_of_term cmpRawIntOp_term
let is_cmpRawIntOp_term = is_dep0_dep0_term cmpRawIntOp_opname
let mk_cmpRawIntOp_term = mk_dep0_dep0_term cmpRawIntOp_opname
let dest_cmpRawIntOp_term = dest_dep0_dep0_term cmpRawIntOp_opname

(* Floats. *)

let plusFloatOp_term = << plusFloatOp{ 'precision } >>
let plusFloatOp_opname = opname_of_term plusFloatOp_term
let is_plusFloatOp_term = is_dep0_term plusFloatOp_opname
let mk_plusFloatOp_term = mk_dep0_term plusFloatOp_opname
let dest_plusFloatOp_term = dest_dep0_term plusFloatOp_opname

let minusFloatOp_term = << minusFloatOp{ 'precision } >>
let minusFloatOp_opname = opname_of_term minusFloatOp_term
let is_minusFloatOp_term = is_dep0_term minusFloatOp_opname
let mk_minusFloatOp_term = mk_dep0_term minusFloatOp_opname
let dest_minusFloatOp_term = dest_dep0_term minusFloatOp_opname

let mulFloatOp_term = << mulFloatOp{ 'precision } >>
let mulFloatOp_opname = opname_of_term mulFloatOp_term
let is_mulFloatOp_term = is_dep0_term mulFloatOp_opname
let mk_mulFloatOp_term = mk_dep0_term mulFloatOp_opname
let dest_mulFloatOp_term = dest_dep0_term mulFloatOp_opname

let divFloatOp_term = << divFloatOp{ 'precision } >>
let divFloatOp_opname = opname_of_term divFloatOp_term
let is_divFloatOp_term = is_dep0_term divFloatOp_opname
let mk_divFloatOp_term = mk_dep0_term divFloatOp_opname
let dest_divFloatOp_term = dest_dep0_term divFloatOp_opname

let remFloatOp_term = << remFloatOp{ 'precision } >>
let remFloatOp_opname = opname_of_term remFloatOp_term
let is_remFloatOp_term = is_dep0_term remFloatOp_opname
let mk_remFloatOp_term = mk_dep0_term remFloatOp_opname
let dest_remFloatOp_term = dest_dep0_term remFloatOp_opname

let maxFloatOp_term = << maxFloatOp{ 'precision } >>
let maxFloatOp_opname = opname_of_term maxFloatOp_term
let is_maxFloatOp_term = is_dep0_term maxFloatOp_opname
let mk_maxFloatOp_term = mk_dep0_term maxFloatOp_opname
let dest_maxFloatOp_term = dest_dep0_term maxFloatOp_opname

let minFloatOp_term = << minFloatOp{ 'precision } >>
let minFloatOp_opname = opname_of_term minFloatOp_term
let is_minFloatOp_term = is_dep0_term minFloatOp_opname
let mk_minFloatOp_term = mk_dep0_term minFloatOp_opname
let dest_minFloatOp_term = dest_dep0_term minFloatOp_opname

let eqFloatOp_term = << eqFloatOp{ 'precision } >>
let eqFloatOp_opname = opname_of_term eqFloatOp_term
let is_eqFloatOp_term = is_dep0_term eqFloatOp_opname
let mk_eqFloatOp_term = mk_dep0_term eqFloatOp_opname
let dest_eqFloatOp_term = dest_dep0_term eqFloatOp_opname

let neqFloatOp_term = << neqFloatOp{ 'precision } >>
let neqFloatOp_opname = opname_of_term neqFloatOp_term
let is_neqFloatOp_term = is_dep0_term neqFloatOp_opname
let mk_neqFloatOp_term = mk_dep0_term neqFloatOp_opname
let dest_neqFloatOp_term = dest_dep0_term neqFloatOp_opname

let ltFloatOp_term = << ltFloatOp{ 'precision } >>
let ltFloatOp_opname = opname_of_term ltFloatOp_term
let is_ltFloatOp_term = is_dep0_term ltFloatOp_opname
let mk_ltFloatOp_term = mk_dep0_term ltFloatOp_opname
let dest_ltFloatOp_term = dest_dep0_term ltFloatOp_opname

let leFloatOp_term = << leFloatOp{ 'precision } >>
let leFloatOp_opname = opname_of_term leFloatOp_term
let is_leFloatOp_term = is_dep0_term leFloatOp_opname
let mk_leFloatOp_term = mk_dep0_term leFloatOp_opname
let dest_leFloatOp_term = dest_dep0_term leFloatOp_opname

let gtFloatOp_term = << gtFloatOp{ 'precision } >>
let gtFloatOp_opname = opname_of_term gtFloatOp_term
let is_gtFloatOp_term = is_dep0_term gtFloatOp_opname
let mk_gtFloatOp_term = mk_dep0_term gtFloatOp_opname
let dest_gtFloatOp_term = dest_dep0_term gtFloatOp_opname

let geFloatOp_term = << geFloatOp{ 'precision } >>
let geFloatOp_opname = opname_of_term geFloatOp_term
let is_geFloatOp_term = is_dep0_term geFloatOp_opname
let mk_geFloatOp_term = mk_dep0_term geFloatOp_opname
let dest_geFloatOp_term = dest_dep0_term geFloatOp_opname

let cmpFloatOp_term = << cmpFloatOp{ 'precision } >>
let cmpFloatOp_opname = opname_of_term cmpFloatOp_term
let is_cmpFloatOp_term = is_dep0_term cmpFloatOp_opname
let mk_cmpFloatOp_term = mk_dep0_term cmpFloatOp_opname
let dest_cmpFloatOp_term = dest_dep0_term cmpFloatOp_opname

let atan2Op_term = << atan2Op{ 'precision } >>
let atan2Op_opname = opname_of_term atan2Op_term
let is_atan2Op_term = is_dep0_term atan2Op_opname
let mk_atan2Op_term = mk_dep0_term atan2Op_opname
let dest_atan2Op_term = dest_dep0_term atan2Op_opname
