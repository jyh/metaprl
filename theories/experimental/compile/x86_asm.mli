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
declare ImmediateLabel{'v}
declare ImmediateCLabel{'v}
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
declare MOV{'dst; 'src}
declare NEG{'dst}
declare NOT{'dst}
declare ADD{'dst; 'src}
declare LEA{'dst; 'src}
declare SUB{'dst; 'src}
declare IMUL{'dst; 'src}

(*!
 * @begin[doc]
 * The @emph{MUL} and @emph{DIV} instructions require that
 * the destination operands be @emph{eax} and @emph{edx},
 * repectively.
 * @end[doc]
 *)
declare MUL{'dst1; 'dst2; 'src}
declare DIV{'dst1; 'dst2; 'src}

declare AND{'dst; 'src}
declare OR{'dst; 'src}
declare XOR{'dst; 'src}
declare SAR{'dst; 'src}
declare SHL{'dst; 'src}
declare SHR{'dst; 'src}

declare TEST{'src1; 'src2}
declare CMP{'src1; 'src2}
declare JMP{'label}
declare JCC{'cc; 'label}
declare IJMP{'params; 'src}
declare SET{'cc; 'dst}

declare GC{'i; 'params}
declare LABEL{'v}

(*!
 * @begin[doc]
 * @modsubsection{Scoping}
 *
 * The variables and labels in the assembly are scoped.
 *)
declare RegDecl{v. 'e['v]}
declare LabelDecl{v. 'e['v]}
declare Label{'label}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
