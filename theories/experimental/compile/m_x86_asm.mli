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
declare SpillMemory{'label}
declare SpillRegister{'v; 'label}
declare ContextRegister[label:t]
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
 * We want the assembly to have "semi-functional" property,
 * meaning that registers are immutable.  The register allocator
 * will coalesce registers, creating implicit assignments
 * in the process.
 *
 * This presents an interesting problem for the x86, since it
 * uses the two-operand instruction form.  To get around this,
 * we define a normal two-operand instruction set for _memory_
 * operands.  Then we define a three-operand set for register
 * destination operands.  Again, the allocator is responsible
 * for making sure the dst and the first src register are the
 * same.
 *
 * Further, for simplicity, we categorize instructions into
 * several kinds.
 *
 * Mov defines a new register from an arbitrary operand
 * Inst1[opname]: a normal one-operand instruction
 * Inst2[opname]: this is a normal two-operand instruction
 * Inst3[opname]: a MUL/DIV instruction
 * Shift[opname]: a shift instruction
 * Cmp[opname]: a comparison; both operands are sources
 * Set[opname]: the set/cc instruction
 * @end[doc]
 *)
declare Mov{'src; dst. 'rest['dst]}
declare Spill[opcode:s]{'src; dst. 'rest['dst]}
declare Inst1[opcode:s]{'dst; 'rest}
declare Inst1[opcode:s]{'src; dst. 'rest['dst]}
declare Inst2[opcode:s]{'src; 'dst; 'rest}
declare Inst2[opcode:s]{'src1; 'src2; dst. 'rest['dst]}
declare Inst3[opcode:s]{'src1; 'src2; 'src3; dst2, dst3. 'rest['dst2; 'dst3]}
declare Shift[opcode:s]{'src; 'dst; 'rest}
declare Shift[opcode:s]{'src1; 'src2; dst. 'rest['dst]}
declare Cmp[opcode:s]{'src1; 'src2; 'rest}
declare Set[opcode:s]{'cc; 'dst; 'rest['dst]}
declare Set[opcode:s]{'cc; 'src; dst. 'rest['dst]}

(*
 * Various forms of tailcalls.
 *)
declare AsmArgNil
declare AsmArgCons{'a; 'rest}
declare Jmp[opcode:s]{'label; 'args}

(*
 * For conditional jumps, pretend that it is a real
 * conditional.  The printer will have to insert a label.
 *)
declare Jcc[opcode:s]{'cc; 'rest1; 'rest2}

(*
 * Reserve some words.
 *)
declare AsmReserve[words:n]{'params}

(*
 * Also add a comment instruction.
 *)
declare Comment[comment:s]{'rest}
declare Init{'rest}

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
