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
declare LT
declare LE
declare EQ
declare NEQ
declare GT
declare GE
declare ULT
declare ULE
declare UGT
declare UGE

(*!
 * @begin[doc]
 * @modsubsection{Instructions}
 * @end[doc]
 *)
declare MOV{'src; dst. 'rest['dst]}
declare MOV{'dst; 'src; 'rest}
declare NEG{'dst; 'rest}
declare NOT{'dst; 'rest}
declare ADD{'dst; 'src; 'rest}
declare LEA{'dst; 'src; 'rest}
declare SUB{'dst; 'src; 'rest}
declare IMUL{'dst; 'src; 'rest}

(*!
 * @begin[doc]
 * The @emph{MUL} and @emph{DIV} instructions require that
 * the destination operands be @emph{eax} and @emph{edx},
 * repectively.
 * @end[doc]
 *)
declare MUL{'dst1; 'dst2; 'src; 'rest}
declare DIV{'dst1; 'dst2; 'src; 'rest}

declare AND{'dst; 'src; 'rest}
declare OR{'dst; 'src; 'rest}
declare XOR{'dst; 'src; 'rest}
declare SAR{'dst; 'src; 'rest}
declare SHL{'dst; 'src; 'rest}
declare SHR{'dst; 'src; 'rest}

declare TEST{'src1; 'src2; 'rest}
declare CMP{'src1; 'src2; 'rest}
declare SET{'cc; 'dst; 'rest}

(*
 * Various forms of tailcalls.
 *)
declare JMP{'label; 'arg1}
declare JMP{'label; 'arg1; 'arg2}
declare JMP{'label; 'arg1; 'arg2; 'arg3}
declare JCC{'cc; 'label; 'arg1; 'rest}
declare JCC{'cc; 'label; 'arg1; 'arg2; 'rest}
declare JCC{'cc; 'label; 'arg1; 'arg2; 'arg3; 'rest}
declare IJMP{'src; 'arg1}
declare IJMP{'src; 'arg1; 'arg2}
declare IJMP{'src; 'arg1; 'arg2; 'arg3}

(*
 * Comment for debugging.
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
