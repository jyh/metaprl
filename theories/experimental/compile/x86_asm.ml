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
 * @end[doc]
 *)
declare RegDecl{v. 'e['v]}
declare LabelDecl{v. 'e['v]}
declare Label{'label}

(************************************************************************
 * Display forms.
 *)
dform immediate_number_df : ImmediateNumber[i:n] =
   `"#" slot[i:n]

dform immediate_label_df : ImmediateLabel{'label} =
   slot{'label}

dform immediate_clabel_df : ImmediateCLabel{'label} =
   slot{'label}

dform register_df : Register{'v} =
   bf["%"] slot{'v}

dform mem_reg_df : MemReg{'r} =
   `"(" slot{'r} `")"

dform mem_reg_off_df : MemRegOff[i:n]{'r} =
   `"(" slot{'r} `"," slot[i:n] `")"

dform mem_reg_reg_off_mul_df : MemRegRegOffMul[off:n, mul:n]{'r1; 'r2} =
   `"(" slot{'r1} `"," slot{'r2} `"," slot[off:n] `"," slot[mul:n] `")"

dform mov_df : MOV{'dst; 'src} =
    `"MOV " slot{'dst} `"," slot{'src}

dform neg_df : NEG{'dst} =
    `"NEG " slot{'dst}

dform not_df : NOT{'dst} =
    `"NOT " slot{'dst}

dform add_df : ADD{'dst; 'src} =
    `"ADD " slot{'dst} `"," slot{'src}

dform lea_df : LEA{'dst; 'src} =
    `"LEA " slot{'dst} `"," slot{'src}

dform sub_df : SUB{'dst; 'src} =
    `"SUB " slot{'dst} `"," slot{'src}

dform imul_df : IMUL{'dst; 'src} =
   space `"IMUL " slot{'dst} `"," slot{'src}

dform mul_df : MUL{'dst1; 'dst2; 'src} =
    `"MUL /* " slot{'dst1} `"," slot{'dst2} `" */ " slot{'src}

dform div_df : DIV{'dst1; 'dst2; 'src} =
    `"DIV /* " slot{'dst1} `"," slot{'dst2} `" */ " slot{'src}

dform and_df : AND{'dst; 'src} =
    `"AND " slot{'dst} `"," slot{'src}

dform or_df : OR{'dst; 'src} =
    `"OR " slot{'dst} `"," slot{'src}

dform xor_df : XOR{'dst; 'src} =
    `"XOR " slot{'dst} `"," slot{'src}

dform sar_df : SAR{'dst; 'src} =
   `"SAR " slot{'dst} `"," slot{'src}

dform shl_df : SHL{'dst; 'src} =
   `"SHL " slot{'dst} `"," slot{'src}

dform shr_df : SHR{'dst; 'src} =
   `"SHR " slot{'dst} `"," slot{'src}

dform test_df : TEST{'src1; 'src2} =
   `"TEST " slot{'src1} `"," slot{'src2}

dform cmp_df : CMP{'src1; 'src2} =
   `"CMP " slot{'src1} `"," slot{'src2}

dform jmp_df : JMP{'label} =
   `"JMP " slot{'label}

dform jcc_eq_df : JCC{EQ; 'label} =
   `"JZ " slot{'label}

dform jcc_neq_df : JCC{NEQ; 'label} =
   `"JNZ " slot{'label}

dform jcc_lt_df : JCC{LT; 'label} =
   `"JLT " slot{'label}

dform jcc_le_df : JCC{LE; 'label} =
   `"JLE " slot{'label}

dform jcc_gt_df : JCC{GT; 'label} =
   `"JGT " slot{'label}

dform jcc_ge_df : JCC{GE; 'label} =
   `"JGE " slot{'label}

dform jcc_ult_df : JCC{ULT; 'label} =
   `"JB " slot{'label}

dform jcc_ule_df : JCC{ULE; 'label} =
   `"JBE " slot{'label}

dform jcc_ugt_df : JCC{UGT; 'label} =
   `"JA " slot{'label}

dform jcc_uge_df : JCC{UGE; 'label} =
   `"JAE " slot{'label}

dform set_eq_df : SET{EQ; 'label} =
   `"SETZ " slot{'label}

dform set_neq_df : SET{NEQ; 'label} =
   `"SETNZ " slot{'label}

dform set_lt_df : SET{LT; 'label} =
   `"SETLT " slot{'label}

dform set_le_df : SET{LE; 'label} =
   `"SETLE " slot{'label}

dform set_gt_df : SET{GT; 'label} =
   `"SETGT " slot{'label}

dform set_ge_df : SET{GE; 'label} =
   `"SETGE " slot{'label}

dform set_ult_df : SET{ULT; 'label} =
   `"SETB " slot{'label}

dform set_ule_df : SET{ULE; 'label} =
   `"SETBE " slot{'label}

dform set_ugt_df : SET{UGT; 'label} =
   `"SETA " slot{'label}

dform set_uge_df : SET{UGE; 'label} =
   `"SETAE " slot{'label}

dform ijmp_df : IJMP{'params; 'src} =
   `"JMP /* " slot{'params} `"*/ *" slot{'src}

dform gc_df : GC{'i; 'params} =
   `"/* GC " slot{'i} `"," slot{'params} `" */"

dform label_df : LABEL{'v} =
   slot{'v} `":"

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
