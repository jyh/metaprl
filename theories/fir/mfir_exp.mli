(*!
 * @begin[doc]
 * @module[Mfir_exp]
 *
 * The @code{Mfir_exp} module declares terms to represent FIR expressions.
 * Expressions in the FIR consist of atoms, operators, and
 * the actual expression forms.
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

extends Base_theory
extends Mfir_ty

(**************************************************************************
 * Declarations.
 **************************************************************************)

(*
 * Unary opeators.
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

declare rawIntOfPointerOp[precision:n, sign:s]
declare pointerOfRawIntOp[precision:n, sign:s]

(*
 * Binary operators.
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

(*
 * Atoms.
 *)

declare atomInt{ 'num }
declare atomEnum[bound:n]{ 'num }
declare atomRawInt[precision:n, sign:s]{ 'num }
declare atomVar{ 'var }
declare atomTyApply{ 'atom; 'ty; 'ty_list }
declare atomTyPack{ 'var; 'ty; 'ty_list }
declare atomTyUnpack{ 'var }
declare atomUnop{ 'unop; 'atom }
declare atomBinop{ 'binop; 'atom1; 'atom2 }

(*
 * Allocation operators.
 *)

declare allocTuple[tc:s]{ 'ty; 'atom_list }
declare allocUnion[case:n]{ 'ty; 'ty_var; 'atom_list }
declare allocVArray{ 'ty; 'atom1; 'atom2 }
declare allocMalloc{ 'ty; 'atom }

(*
 * Expressions.
 *)

declare letAtom{ 'ty; 'atom; var. 'exp['var] }
declare letExt[str:s]{ 'fun_res_type; 'fun_arg_types; 'fun_args; v. 'exp['v] }
declare tailCall{ 'atom; 'atom_list }
declare matchCase{ 'set; 'exp }
declare matchExp{ 'atom; 'matchCase_list }
declare letAlloc{ 'alloc_op; v. 'exp['v] }
declare letSubscript{ 'ty; 'atom1; 'atom2; v. 'exp['v] }
declare setSubscript{ 'atom1; 'atom2; 'ty; 'atom3; 'exp }
declare letGlobal{ 'ty; 'label; v. 'exp['v] }
declare setGlobal{ 'label; 'ty; 'atom; 'exp }
