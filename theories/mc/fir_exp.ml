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
include Itt_theory
include Fir_state
include Fir_int_set
include Fir_ty

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Identity (polymorphic). *)
declare idOp

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

(*
 * Misc.
 *)

declare unknownFun
declare unknownSet
declare unknownAtom
declare unknownAlloc

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Identity (polymorphic). *)
dform idOp_df : except_mode[src] :: idOp = `"id"

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

(* Misc. *)
dform unknownFun_df : except_mode[src] :: unknownFun = `"UnknownFun"
dform unknownSet_df : except_mode[src] :: unknownSet = `"UnknownSet"
dform unknownAtom_df : except_mode[src] :: unknownAtom = `"UnknownAtom"
dform unknownAlloc_df : except_mode[src] :: unknownAlloc = `"UnknownAlloc"

(*************************************************************************
 * Rewrites.
 *************************************************************************)

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
prim_rw reduce_match_block :
   "match"{ block{ number[i:n]; 'args };
      cons{ matchCase{'set; 'e }; 'el } } <-->
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

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << unop_exp{ idOp; 'a1 } >>, reduce_idOp;
   << binop_exp{ eqEqOp; 'a1; 'a2 } >>, reduce_eqEqOp;
   << binop_exp{ neqEqOp; 'a1; 'a2 } >>, reduce_neqEqOp;
   << atomInt{ 'num } >>, reduce_atomInt;
   << atomEnum{ 'bound; 'num } >>, reduce_atomEnum;
   << atomRawInt{ 'num } >>, reduce_atomRawInt;
   << atomVar{ 'var } >>, reduce_atomVar;
   << letUnop{ 'op; 'ty; 'a1; v. 'exp['v] } >>,
      reduce_letUnop;
   << letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp['v] } >>,
      reduce_letBinop;
   << letExt{ 'ty; 'string; 'ty_str; 'atom_list; v. 'exp['v] } >>,
      reduce_letExt;
   << "match"{ number[i:n]; cons{ matchCase{'set; 'e }; 'el } } >>,
      reduce_match_int;
   << "match"{ block{ number[i:n]; 'args };
      cons{ matchCase{'set; 'e }; 'el } } >>,
      reduce_match_block;
   << letAlloc{ allocTuple{ 'ty; 'atom_list }; v. 'exp['v] } >>,
      reduce_allocTuple;
   << letAlloc{ allocArray{ 'ty; 'atom_list }; v. 'exp['v] } >>,
      reduce_allocArray;
   << letSubscript{ 'subop; 'ty; 'ref; 'index; v. 'exp['v] } >>,
      reduce_letSubscript;
   << setSubscript{ 'subop; 'ty; 'var; 'index; 'new_val; v. 'exp['v] } >>,
      reduce_setSubscript
]
