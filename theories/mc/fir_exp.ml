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

(* Identity (polymorphic). *)
declare idOp

(*
 * Naml integer operations.
 *)

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

(*
 * End Naml integer operations.
 *)

(* Pointer equality. *)
declare eqEqOp
declare neqEqOp

(* Subscript operators. *)
declare blockPolySub
declare blockRawIntSub{ 'precision; 'sign }
declare blockFloatSub{ 'precision }
declare rawRawIntSub{ 'precision; 'sign }
declare rawFloatSub{ 'precision }
declare rawDataSub
declare rawFunctionSub

(* Allocation operators. *)
declare allocTuple{ 'ty; 'atom_list }
declare allocArray{ 'ty; 'atom_list }
declare allocUnion{ 'ty; 'ty_var; 'num; 'atom_list }
declare allocMalloc{ 'atom }

(* Normal values. *)
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
declare unop_exp{ 'op; 'a1 }
declare binop_exp{ 'op; 'a1; 'a2 }
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

(* Identity (polymorphic). *)
dform idOp_df : except_mode[src] :: idOp = `"id"

(*
 * Naml integer operations.
 *)

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

(*
 * End Naml integer operations.
 *)

(* Pointer equality. *)
dform eqEqOp_df : except_mode[src] :: eqEqOp = `"EqEqOp"
dform neqEqOp_df : except_mode[src] :: neqEqOp = `"NeqEqOp"

(* Subscript operators. *)
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

(* Allocation operators. *)
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

(* Normal values. *)
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
dform unop_exp_df : except_mode[src] :: unop_exp{ 'op; 'a1 } =
   slot{'op} `"(" slot{'a1} `")"
dform binop_exp_df : except_mode[src] :: binop_exp{ 'op; 'a1; 'a2 } =
   `"(" slot{'a1} `" " slot{'op} `" " slot{'a2} `")"
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

(* Allocation *)
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
