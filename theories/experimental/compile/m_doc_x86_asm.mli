(*
 * Explains CPS conversion.
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
extends M_doc_ir

(*
 * Display the var with a lambda.
 *)
declare math_dst{'dst}

(*
 * Operands.
 *)
declare math_ImmediateNumber{'i}
declare math_ImmediateLabel{'R; 'label}
declare math_ImmediateCLabel{'R; 'label}
declare math_Register{'v}
declare math_SpillMemory{'label}
declare math_SpillRegister{'v; 'label}
declare math_ContextRegister[label:s]
declare math_MemReg{'r}
declare math_MemRegOff{'r; 'i}
declare math_MemRegRegOffMul{'r1; 'r2; 'off; 'mul}

(*
 * Condition codes.
 *)
declare math_CC[code:s]

(*
 * Instructions.
 *)
declare math_Mov{'src; 'dst; 'rest}
declare math_Spill[opcode:s]{'src; 'dst; 'rest}
declare math_Inst1Mem[opcode:s]{'dst; 'rest}
declare math_Inst1Reg[opcode:s]{'src; 'dst; 'rest}
declare math_Inst2Mem[opcode:s]{'src; 'dst; 'rest}
declare math_Inst2Reg[opcode:s]{'src1; 'src2; 'dst; 'rest}
declare math_Inst3Reg[opcode:s]{'src1; 'src2; 'src3; 'dst2; 'dst3; 'rest}
declare math_ShiftMem[opcode:s]{'src; 'dst; 'rest}
declare math_ShiftReg[opcode:s]{'src1; 'src2; 'dst; 'rest}
declare math_Cmp[opcode:s]{'src1; 'src2; 'rest}
declare math_SetMem[opcode:s]{'cc; 'dst; 'rest}
declare math_SetReg[opcode:s]{'cc; 'src; 'dst; 'rest}

(*
 * Various forms of tailcalls.
 * The tailcall takes the arguments in a list.
 *)
declare math_Jmp[opcode:s]{'label; 'args}

(*
 * For conditional jumps, pretend that it is a real
 * conditional.  The printer will have to insert a label.
 *)
declare math_Jcc[opcode:s]{'cc; 'rest1; 'rest2}

(*
 * Reserve some words.
 * The params are the live registers (normally the parameters
 * to the current function).
 *)
declare math_AsmReserve{'words; 'e}
declare math_AsmReserve{'words}

(*
 * Also add a comment instruction.
 *)
declare math_Comment{'comment; 'rest}

(*
 * The program initialization is wrapped in
 * the Init term; we don't include the initialization
 * code in the program output.
 *)
declare math_Init{'rest}

(*
 * Programs.
 *)
declare math_LabelAsm{'R; 'label}

declare math_LabelRec{'R; 'fields; 'rest}
declare math_LabelDef{'label; 'code; 'rest}
declare math_LabelEnd

declare math_LabelFun{'v; 'insts}

(************************************************************************
 * Non-nested versions.
 *)
declare math_Mov{'src; 'dst}
declare math_Spill[opcode:s]{'src; 'dst}
declare math_Inst1Mem[opcode:s]{'dst}
declare math_Inst1Reg[opcode:s]{'src; 'dst}
declare math_Inst2Mem[opcode:s]{'src; 'dst}
declare math_Inst2Reg[opcode:s]{'src1; 'src2; 'dst}
declare math_Inst3Reg[opcode:s]{'src1; 'src2; 'src3; 'dst2; 'dst3}
declare math_ShiftMem[opcode:s]{'src; 'dst}
declare math_ShiftReg[opcode:s]{'src1; 'src2; 'dst}
declare math_Cmp[opcode:s]{'src1; 'src2}
declare math_SetMem[opcode:s]{'cc; 'dst}
declare math_SetReg[opcode:s]{'cc; 'src; 'dst}
declare math_Jcc[opcode:s]{'cc; 'e}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
