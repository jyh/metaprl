(*!
 * @spelling{rawdata tyEnum}
 *
 * @begin[doc]
 * @module[Mfir_exp]
 *
 * The @tt[Mfir_exp] module declares terms to represent FIR expressions.
 * @end[doc]
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
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
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)

extends Mfir_ty


(**************************************************************************
 * Declarations.
 **************************************************************************)

(*
 * DROPPED: PointerOfBlockOp.    Contains a sub_block.
 * DROPPED: PlusPointerOp.       Contains a sub_block.
 * DROPPED: frame_label.         Can fold this into AtomLabel.
 * DROPPED: AtomNil.             Not sure if this is sound.
 * TODO:    AtomFloat.           MetaPRL doesn't have floats.
 * TODO:    AtomLabel.           I'm lazy.
 * TODO:    AtomSizeof.          I'm lazy.
 * TODO:    AtomConst.           I'm lazy.
 * DROPPED: AtomFun.             Not sure if this is really needed. (BUG?)
 * DROPPED: AtomRawDataOfFrame.  No idea what this is for.
 * DROPPED: debugging.           Contains no useful (formal) content.
 * DROPPED: AllocArray.          No idea how this works.
 * TODO:    AllocFrame.          I'm lazy/confused.
 * TODO:    tailop.              I'm lazy.
 * DROPPED: pred.                Unsound implementation in MCC.
 * TODO:    SpecialCall          Blocks on implementing tailop.
 * DROPPED: TypeCase             Part of the (unsound) FIR object system.
 * DROPPED: Memcpy.              Not dealing with this yet.
 * DROPPED: Call.                No idea what this does.
 * DROPPED: Assert.              No idea what this does.
 * DROPPED: Debug.               Contains no useful (formal) content.
 *)

(*
 * BUG: I don't think I need AtomFun.  So it's been dropped for now.
 *)


(*!
 * @begin[doc]
 * @terms
 * @modsubsection{Unary operators}
 *
 * The FIR unary operators include a polymorphic identity operator, various
 * arithmetic operators, and coercion operators that safely transform a value
 * between two types.  We omit an explicit listing these terms.
 * @end[doc]
 * @docoff
 *)

declare idOp
declare uminusIntOp
declare notIntOp

declare rawBitFieldOp[precision:n, sign:s]{ 'num1; 'num2 }

declare uminusRawIntOp[precision:n, sign:s]
declare notRawIntOp[precision:n, sign:s]

declare uminusFloatOp[precision:n]
declare absFloatOp[precision:n]
declare sinOp[precision:n]
declare cosOp[precision:n]
declare sqrtOp[precision:n]

declare intOfFloatOp[precision:n]

declare floatOfIntOp[precision:n]
declare floatOfFloatOp[dest_prec:n, src_prec:n]
declare floatOfRawIntOp[float_prec:n, int_prec:n, int_sign:s]

declare rawIntOfIntOp[precision:n, sign:s]
declare rawIntOfEnumOp[precision:n, sign:s, i:n]
declare rawIntOfFloatOp[int_prec:n, int_sign:s, float_prec:n]
declare rawIntOfRawIntOp[dest_prec:n, dest_sign:s, src_prec:n, src_sign:s]


(*!
 * @begin[doc]
 * @modsubsection{Binary operators}
 *
 * The FIR binary operators include various arithmetic operators, and pointer
 * equality operators. We omit an explicit listing of these terms.
 * @end[doc]
 * @docoff
 *)

declare andEnumOp[i:n]
declare orEnumOp[i:n]
declare xorEnumOp[i:n]

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

declare plusRawIntOp[precision:n, sign:s]
declare minusRawIntOp[precision:n, sign:s]
declare mulRawIntOp[precision:n, sign:s]
declare divRawIntOp[precision:n, sign:s]
declare remRawIntOp[precision:n, sign:s]
declare slRawIntOp[precision:n, sign:s]
declare srRawIntOp[precision:n, sign:s]
declare andRawIntOp[precision:n, sign:s]
declare orRawIntOp[precision:n, sign:s]
declare xorRawIntOp[precision:n, sign:s]
declare maxRawIntOp[precision:n, sign:s]
declare minRawIntOp[precision:n, sign:s]

declare rawSetBitFieldOp[precision:n, sign:s]{ 'num1; 'num2 }

declare eqRawIntOp[precision:n, sign:s]
declare neqRawIntOp[precision:n, sign:s]
declare ltRawIntOp[precision:n, sign:s]
declare leRawIntOp[precision:n, sign:s]
declare gtRawIntOp[precision:n, sign:s]
declare geRawIntOp[precision:n, sign:s]
declare cmpRawIntOp[precision:n, sign:s]

declare plusFloatOp[precision:n]
declare minusFloatOp[precision:n]
declare mulFloatOp[precision:n]
declare divFloatOp[precision:n]
declare remFloatOp[precision:n]
declare maxFloatOp[precision:n]
declare minFloatOp[precision:n]

declare eqFloatOp[precision:n]
declare neqFloatOp[precision:n]
declare ltFloatOp[precision:n]
declare leFloatOp[precision:n]
declare gtFloatOp[precision:n]
declare geFloatOp[precision:n]
declare cmpFloatOp[precision:n]

declare atan2Op[precision:n]

declare eqEqOp
declare neqEqOp


(*!
 * @begin[doc]
 * @modsubsection{Atoms}
 *
 * Atoms represent values, including numbers, variables, and basic arithmetic.
 * Apart from arithmetic exceptions, such as division by zero, they are
 * functional; the order of atom evaluation does not matter.
 *
 * The term @tt[atomInt] corresponds to integers of type @hrefterm[tyInt]. The
 * term @tt[atomEnum] corresponds to constants of type @hrefterm[tyEnum].  The
 * term @tt[atomRawInt] is an integer of type @hrefterm[tyRawInt]. The
 * parameters of these terms specify the relevant parameters of their
 * respective types, and their subterms specify their values.
 * @end[doc]
 *)

declare atomInt{ 'num }
declare atomEnum[bound:n]{ 'num }
declare atomRawInt[precision:n, sign:s]{ 'num }

(*!
 * @begin[doc]
 *
 * The term @tt[atomVar] is used to represent variables in the FIR.
 * @end[doc]
 *)

declare atomVar{ 'var }

(*!
 * @begin[doc]
 *
 * The term @tt[atomTyApply] is the polymorphic type application of an atom
 * @tt[atom] to a list of type arguments @tt[ty_list].  The second subterm is
 * the type of the @tt[atomTyApply] atom.
 * @end[doc]
 *)

declare atomTyApply{ 'atom; 'ty; 'ty_list }

(*!
 * @begin[doc]
 *
 * The term @tt[atomTyPack] abstracts a variable @tt[var] over a list of types
 * @tt[ty_list].  The second subterm is the type of the @tt[atomTyPack] atom.
 * @end[doc]
 *)

declare atomTyPack{ 'var; 'ty; 'ty_list }

(*!
 * @begin[doc]
 *
 * The term @tt[atomTyUnpack] is the elimination form for type abstraction.
 * The variable @tt[var] is instantiated with the types from the original pack
 * operation.
 * @end[doc]
 *)

declare atomTyUnpack{ 'var }

(*!
 * @begin[doc]
 *
 * The FIR supports both unary and binary arithmetic. The term @tt[atomUnop]
 * has subterms for a unary operator and its argument.  The term
 * @tt[atomBinop] has subterms for a binary operator and its two arguments.
 * @end[doc]
 *)

declare atomUnop{ 'unop; 'atom }
declare atomBinop{ 'binop; 'atom1; 'atom2 }


(*!
 * @begin[doc]
 * @modsubsection{Allocation operators}
 *
 * Allocation operators are used in the @hrefterm[letAlloc] expression below
 * to allocate data aggregates.  The term @tt[allocTuple] is used to allocate
 * a tuple value with type @tt[ty], tuple class @tt[tc], and elements
 * @tt[atom_list].
 * @end[doc]
 *)

declare allocTuple[tc:s]{ 'ty; 'atom_list }

(*!
 * @begin[doc]
 *
 * The term @tt[allocUnion] is used to allocate a union value of type @tt[ty].
 * The union definition is given by @tt[ty_var], and the case allocated is
 * given by @tt[case].  The list @tt[atom_list] contains the atoms used to
 * initialize the case.
 * @end[doc]
 *)

declare allocUnion[case:n]{ 'ty; 'ty_var; 'atom_list }

(*!
 * @begin[doc]
 *
 * The term @tt[allocVArray] allocates an array of size @tt[atom1] of type
 * @tt[ty].  All the elements of the array are initialized to @tt[atom2].
 * @end[doc]
 *)

declare allocVArray{ 'ty; 'atom1; 'atom2 }

(*!
 * @begin[doc]
 *
 * The term @tt[allocMalloc] is used to allocate a rawdata block with type
 * @tt[ty].  The size of the allocated area is given by @tt[atom].
 * @end[doc]
 *)

declare allocMalloc{ 'ty; 'atom }


(*!
 * @begin[doc]
 * @modsubsection{Expressions}
 *
 * Expressions combine the atoms and operators above to define FIR
 * programs. They include forms for binding values to variables,
 * calling functions, matching a value against a pattern, allocating data,
 * and subscripting aggregate data.
 *
 * The term @tt[letAtom] forms a new scope, where an atom @tt[atom] of
 * type @tt[ty] is bound to @tt[v] in @tt[exp].
 * @end[doc]
 *)

declare letAtom{ 'ty; 'atom; v. 'exp['v] }

(*!
 * @begin[doc]
 *
 * The term @tt[letExt] is used to access a function @tt[str] that is part of
 * the runtime or operating system.  The function has argument types
 * @tt[fun_arg_types], returns a result of type @tt[fun_res_type], and is
 * called with arguments @tt[fun_args].  The value returned is bound to @tt[v]
 * in @tt[exp].
 * @end[doc]
 *)

declare letExt[str:s]{ 'fun_res_type; 'fun_arg_types; 'fun_args; v. 'exp['v] }

(*!
 * @begin[doc]
 *
 * The term @tt[tailCall] is a function call to the function given by
 * @tt[atom].  The arguments to the function are given by @tt[atom_list].
 * There is no way to bind the value returned by the function.
 * @end[doc]
 *)

declare tailCall{ 'atom; 'atom_list }

(*!
 * @begin[doc]
 *
 * The term @tt[matchExp] is a pattern matching expression that matches an
 * atom @tt[atom] against a list of cases @tt[matchCase_list]. A match case is
 * specified by the term @tt[matchCase], which takes a set (either an integer
 * set or a raw integer set) @tt[set], and an expression @tt[exp].
 * Operationally, the first case for which @tt[atom] is an element of the
 * case's set is selected for evaluation.
 * @end[doc]
 *)

declare matchCase{ 'set; 'exp }
declare matchExp{ 'atom; 'matchCase_list }

(*!
 * @begin[doc]
 *
 * The @tt[letAlloc] term is used to allocate a data aggregate using
 * @tt[alloc_op].  A pointer to the allocated area is bound to @tt[v]
 * in @tt[exp].
 * @end[doc]
 *)

declare letAlloc{ 'alloc_op; v. 'exp['v] }

(*!
 * @begin[doc]
 *
 * The terms @tt[letSubscript] and @tt[setSubscript] are used to subscript
 * data aggregates.  In both terms, @tt[atom1] refers to a data aggregate,
 * and @tt[atom2] is an index into @tt[atom1].  The value at that location
 * should have type @tt[ty].  In the case of @tt[letSubscript], the value is
 * bound to @tt[v] in @tt[exp].  In the case of @tt[setSubscript], the value
 * is set to @tt[atom3].
 * @end[doc]
 *)

declare letSubscript{ 'ty; 'atom1; 'atom2; v. 'exp['v] }
declare setSubscript{ 'atom1; 'atom2; 'ty; 'atom3; 'exp }

(*!
 * @begin[doc]
 *
 * The term @tt[letGlobal] is used to bind the value of global variable
 * @tt[label], of type @tt[ty], to @tt[v] in @tt[exp]. The term @tt[setGlobal]
 * is used to set the value of a global variable @tt[label], of type @tt[ty],
 * to the value @tt[atom].
 * @end[doc]
 *)

declare letGlobal{ 'ty; 'label; v. 'exp['v] }
declare setGlobal{ 'label; 'ty; 'atom; 'exp }

(*!
 * @docoff
 *)


(**************************************************************************
 * Display forms.
 **************************************************************************)

(*
 * Unary operators.
 *)

(* NOTE: Implementing these as needed. *)

dform uminusIntOp_df1 : except_mode[src] :: except_mode[tex] ::
   uminusIntOp =
   `"~-" sub{tyInt}

dform uminusIntOp_df2 : mode[tex] ::
   uminusIntOp =
   izone `"\\sim\\!\\!-" ezone sub{tyInt}

(*
 * Binary operators.
 *)

(* NOTE: Implementing these as needed. *)

dform plusIntOp_df : except_mode[src] ::
   plusIntOp =
   `"+" sub{tyInt}

(*
 * Atoms.
 *)

dform atomInt_df : except_mode[src] ::
   atomInt{ 'num } =
   bf["int"] `"(" slot{'num} `")"

dform atomEnum_df : except_mode[src] ::
   atomEnum[bound:n]{ 'num } =
   bf["enum"] sub{slot[bound:n]} `"(" slot{'num} `")"

dform atomRawInt_df1 : except_mode[src] ::
   atomRawInt[precision:n, sign:s]{ 'num } =
   bf["rawint"] sub{slot[precision:n]} sup{slot[sign:s]}
      `"(" slot{'num} `")"

dform atomRawInt_df2 : except_mode[src] ::
   atomRawInt[precision:n, "signed"]{ 'num } =
   bf["rawint"] sub{slot[precision:n]} sup{bf["signed"]}
      `"(" slot{'num} `")"

dform atomRawInt_df3 : except_mode[src] ::
   atomRawInt[precision:n, "unsigned"]{ 'num } =
   bf["rawint"] sub{slot[precision:n]} sup{bf["unsigned"]}
      `"(" slot{'num} `")"

dform atomVar_df : except_mode[src] ::
   atomVar{ 'var } =
   bf["var"] `"(" slot{'var} `")"

dform atomTyApply_df : except_mode[src] ::
   atomTyApply{ 'atom; 'ty; 'ty_list } =
   bf["apply"] `"[" slot{'ty} `"]("
      slot{'atom} `", " slot{'ty_list} `")"

dform atomTyPack_df : except_mode[src] ::
   atomTyPack{ 'var; 'ty; 'ty_list } =
   bf["pack"] `"[" slot{'ty} `"]("
      slot{'var} `", " slot{'ty_list} `")"

dform atomTyUnpack_df : except_mode[src] ::
   atomTyUnpack{ 'var } =
   bf["unpack"] `"(" slot{'var} `")"

dform atomUnop_df : except_mode[src] ::
   atomUnop{ 'unop; 'atom } =
   `"(" slot{'unop} `" " slot{'atom} `")"

dform atomBinop_df : except_mode[src] ::
   atomBinop{ 'binop; 'atom1; 'atom2 } =
   `"(" slot{'atom1} `" " slot{'binop} `" " slot{'atom2} `")"

(*
 * Allocation operators.
 *)

dform allocTuple_df : except_mode[src] ::
   allocTuple[tc:s]{ 'ty; 'atom_list } =
   bf["alloc "] slot{'atom_list} sub{slot[tc:s]} `": " slot{'ty}

dform allocUnion_df : except_mode[src] ::
   allocUnion[case:n]{ 'ty; 'ty_var; 'atom_list } =
   bf["alloc union"] `"(" slot{'ty_var} `"(" slot{'atom_list} `"),"
      slot[case:n] `"): " slot{'ty}

dform allocVArray_df : except_mode[src] ::
   allocVArray{ 'ty; 'atom1; 'atom2 } =
   bf["alloc array"] `"(" slot{'atom1} `", " slot{'atom2} `"): "
      slot{'ty}

dform allocMalloc_df : except_mode[src] ::
   allocMalloc{ 'ty; 'atom } =
   bf["alloc malloc"] `"(" slot{'atom} `"): " slot{'ty}

(*
 * Expressions.
 *)

dform letAtom_df : except_mode[src] ::
   letAtom{ 'ty; 'atom; v. 'exp } =
   pushm[0] szone push_indent bf["let "]
      slot{'v} `":" slot{'ty} `"=" hspace
      szone slot{'atom} ezone popm hspace
      push_indent bf["in"] hspace
      szone slot{'exp} ezone popm
      ezone popm

dform letExt_df : except_mode[src] ::
   letExt[str:s]{ 'fun_res_type; 'fun_arg_types; 'fun_args; v. 'exp } =
   pushm[0] szone push_indent bf["let "] slot{'v} `"=" hspace
      szone slot[str:s] `"(" slot{'fun_args} `"):"
         tyFun{'fun_arg_types; 'fun_res_type} ezone popm hspace
      push_indent bf["in"] hspace
      szone slot{'exp} ezone popm
      ezone popm

dform tailCall_df : except_mode[src] ::
   tailCall{ 'atom; 'atom_list } =
   slot{'atom} `"(" slot{'atom_list} `")"

dform matchCase_df : except_mode[src] ::
   matchCase{ 'set; 'exp } =
   pushm[0] szone push_indent slot{'set} `"->" hspace
   szone slot{'exp} ezone popm
   ezone popm

dform matchExp_df : except_mode[src] ::
   matchExp{ 'atom; 'matchCase_list } =
   pushm[0] szone push_indent bf["match"]  hspace
   szone slot{'atom} ezone popm hspace
   push_indent bf["in"] hspace
   szone slot{'matchCase_list} ezone popm
   ezone popm

dform letAlloc_df : except_mode[src] ::
   letAlloc{ 'alloc_op; v. 'exp } =
   pushm[0] szone push_indent bf["let "] slot{'v} `"=" hspace
      szone slot{'alloc_op} ezone popm hspace
      push_indent bf["in"] hspace
      szone slot{'exp} ezone popm
      ezone popm

dform letSubscript_df : except_mode[src] ::
   letSubscript{ 'ty; 'atom1; 'atom2; v. 'exp } =
   pushm[0] szone push_indent bf["let "]
      slot{'v} `":" slot{'ty} `"=" hspace
      szone slot{'atom1} `"[" slot{'atom2} `"]" ezone popm hspace
      push_indent bf["in"] hspace
      szone slot{'exp} ezone popm
      ezone popm

dform setSubscript_df : except_mode[src] ::
   setSubscript{ 'atom1; 'atom2; 'ty; 'atom3; 'exp } =
   slot{'atom1} `"[" slot{'atom2} `"]:" slot{'ty}
      leftarrow slot{'atom3} `";" hspace
      slot{'exp}

dform letGlobal_df : except_mode[src] ::
   letGlobal{ 'ty; 'label; v. 'exp } =
   pushm[0] szone push_indent bf["let "]
      slot{'v} `":" slot{'ty} `"=" hspace
      szone slot{'label} ezone popm hspace
      push_indent bf["in"] hspace
      szone slot{'exp} ezone popm
      ezone popm

dform setGlobal_df : except_mode[src] ::
   setGlobal{ 'label; 'ty; 'atom; 'exp } =
   slot{'label} `":" slot{'ty} leftarrow slot{'atom} `";" slot{'exp}
