(*
 * This module define x86 assembly code.
 * The one difference here is that we continue to
 * use variable scoping.
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

extends Base_theory

(* x86 operands *)
declare ImmediateNumber[i:n]
declare ImmediateLabel[label:s]{'R}
declare ImmediateCLabel[label:s]{'R}
declare Register{'v}
declare SpillMemory{'label}
declare SpillRegister{'v; 'label}
declare ContextRegister[label:s]
declare MemReg{'r}
declare MemRegOff[i:n]{'r}
declare MemRegRegOffMul[off:n, mul:n]{'r1; 'r2}

(* Condition codes *)
declare CC[cc:s]

(* Instructions *)
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

(* Programs *)
declare LabelAsm[label:s]{'R}

declare LabelRec{R1. 'fields['R1]; R2. 'rest['R2]}
declare LabelDef{'label; 'code; 'rest}
declare LabelEnd

declare LabelFun{v. 'insts['v]}

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
