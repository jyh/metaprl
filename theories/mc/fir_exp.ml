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
declare atomRawInt{ 'num }
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
dform atomRawInt_df : except_mode[src] :: atomRawInt{ 'num } =
   lzone `"AtomRawInt(" slot{'num} `")" ezone
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
