(*!
 * @begin[doc]
 * @module[Assembly]
 *
 * This module define x86 assembly code.
 * The one difference here is that we continue to
 * use variable scoping.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
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
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Base_theory
(*! @docoff *)

(*!
 * @begin[doc]
 * @modsubsection{x86 operands}
 * @end[doc]
 *)
declare ImmediateNumber[i:n]
declare ImmediateLabel[label:t]{'R}
declare ImmediateCLabel[label:t]{'R}
declare Register{'v}
declare SpillRegister{'v}
declare MemReg{'r}
declare MemRegOff[i:n]{'r}
declare MemRegRegOffMul[off:n, mul:n]{'r1; 'r2}

(*!
 * @begin[doc]
 * @modsubsection{Condition codes}
 * @end[doc]
 *)
declare CC["lt"]
declare CC["le"]
declare CC["z"]
declare CC["nz"]
declare CC["gt"]
declare CC["ge"]
declare CC["b"]
declare CC["be"]
declare CC["a"]
declare CC["ae"]

(*!
 * @begin[doc]
 * @modsubsection{Instructions}
 *
 * There are several classes of instructions.
 *
 * let defines a new registers
 * Inst2[opname]: this is a normal two-operand instruction
 * Inst1[opname]: a normal one-operand instruction
 * Instm[opname]: a MUL/DIV instruction
 * Shift[opname]: a shift instruction; if the second operand is
 *   not a constant, it must be register %cl
 * Cmp[opname]: a comparison; both operands are sources
 * Set[opname]: the set/cc instruction
 * @end[doc]
 *)
declare Let{'src; dst. 'rest['dst]}
declare Inst1["neg"]{'dst; 'rest}
declare Inst1["not"]{'dst; 'rest}
declare Inst2["mov"]{'dst; 'src; 'rest}
declare Inst2["add"]{'dst; 'src; 'rest}
declare Inst2["lea"]{'dst; 'src; 'rest}
declare Inst2["sub"]{'dst; 'src; 'rest}
declare Inst2["imul"]{'dst; 'src; 'rest}

(*!
 * @begin[doc]
 * The @emph{MUL} and @emph{DIV} instructions require that
 * the destination operands be @emph{eax} and @emph{edx},
 * repectively.
 * @end[doc]
 *)
declare Instm["mul"]{'dst1; 'dst2; 'src; 'rest}
declare Instm["div"]{'dst1; 'dst2; 'src; 'rest}

declare Inst2["and"]{'dst; 'src; 'rest}
declare Inst2["or"]{'dst; 'src; 'rest}
declare Inst2["xor"]{'dst; 'src; 'rest}
declare Shift["sar"]{'dst; 'src; 'rest}
declare Shift["shl"]{'dst; 'src; 'rest}
declare Shift["shr"]{'dst; 'src; 'rest}

declare Cmp["test"]{'src1; 'src2; 'rest}
declare Cmp["cmp"]{'src1; 'src2; 'rest}
declare Set["set"]{'cc; 'dst; 'rest}

(*
 * Various forms of tailcalls.
 *)
declare Jmp["jmp"]{'label; 'arg1}
declare Jmp["jmp"]{'label; 'arg1; 'arg2}
declare Jmp["jmp"]{'label; 'arg1; 'arg2; 'arg3}
declare Jcc["jcc"]{'cc; 'label; 'arg1; 'rest}
declare Jcc["jcc"]{'cc; 'label; 'arg1; 'arg2; 'rest}
declare Jcc["jcc"]{'cc; 'label; 'arg1; 'arg2; 'arg3; 'rest}

(*
 * Also add a comment instruction.
 *)
declare Comment[comment:s]{'rest}

(*!
 * @begin[doc]
 * @modsubsection{Programs}
 *
 * A program is a set of recursive definitions.
 * @end[doc]
 *)
declare LabelAsm[label:t]{'R}

declare LabelRec{R1. 'fields['R1]; R2. 'rest['R2]}
declare LabelDef{'label; 'code; 'rest}
declare LabelEnd

declare LabelFun{v. 'insts['v]}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
