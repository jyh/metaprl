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

(************************************************************************
 * Display forms.
 *)
dform immediate_number_df : ImmediateNumber[i:n] =
   `"#" slot[i:n]

dform immediate_label_df : ImmediateLabel[label:t]{'R} =
   slot{'R} `"." slot[label:t]

dform immediate_clabel_df : ImmediateCLabel[label:t]{'R} =
   `"$" slot{'R} `"." slot[label:t]

dform register_df : Register{'v} =
   `"%" slot{'v}

dform mem_reg_df : MemReg{'r} =
   `"(%" slot{'r} `")"

dform mem_reg_off_df : MemRegOff[i:n]{'r} =
   `"(%" slot{'r} `"," slot[i:n] `")"

dform mem_reg_reg_off_mul_df : MemRegRegOffMul[off:n, mul:n]{'r1; 'r2} =
   `"(%" slot{'r1} `",%" slot{'r2} `"," slot[off:n] `"," slot[mul:n] `")"

dform mov_df : MOV{'dst; 'src; 'rest} =
    `"MOV " slot{'dst} `"," slot{'src} hspace slot{'rest}

dform mov_df : MOV{'src; dst. 'rest} =
    `"MOV %" slot{'dst} `", " slot{'src} `" /* LET */" hspace slot{'rest}

dform neg_df : NEG{'dst; 'rest} =
    `"NEG " slot{'dst} hspace slot{'rest}

dform not_df : NOT{'dst; 'rest} =
    `"NOT " slot{'dst} hspace slot{'rest}

dform add_df : ADD{'dst; 'src; 'rest} =
    `"ADD " slot{'dst} `", " slot{'src} hspace slot{'rest}

dform lea_df : LEA{'dst; 'src; 'rest} =
    `"LEA " slot{'dst} `", " slot{'src} hspace slot{'rest}

dform sub_df : SUB{'dst; 'src; 'rest} =
    `"SUB " slot{'dst} `", " slot{'src} hspace slot{'rest}

dform imul_df : IMUL{'dst; 'src; 'rest} =
   space `"IMUL " slot{'dst} `", " slot{'src} hspace slot{'rest}

dform mul_df : MUL{'dst1; 'dst2; 'src; 'rest} =
    `"MUL /* " slot{'dst1} `", " slot{'dst2} `" */ " slot{'src} hspace slot{'rest}

dform div_df : DIV{'dst1; 'dst2; 'src; 'rest} =
    `"DIV /* " slot{'dst1} `", " slot{'dst2} `" */ " slot{'src} hspace slot{'rest}

dform and_df : AND{'dst; 'src; 'rest} =
    `"AND " slot{'dst} `", " slot{'src} hspace slot{'rest}

dform or_df : OR{'dst; 'src; 'rest} =
    `"OR " slot{'dst} `", " slot{'src} hspace slot{'rest}

dform xor_df : XOR{'dst; 'src; 'rest} =
    `"XOR " slot{'dst} `", " slot{'src} hspace slot{'rest}

dform sar_df : SAR{'dst; 'src; 'rest} =
   `"SAR " slot{'dst} `", " slot{'src} hspace slot{'rest}

dform shl_df : SHL{'dst; 'src; 'rest} =
   `"SHL " slot{'dst} `", " slot{'src} hspace slot{'rest}

dform shr_df : SHR{'dst; 'src; 'rest} =
   `"SHR " slot{'dst} `", " slot{'src} hspace slot{'rest}

dform test_df : TEST{'src1; 'src2; 'rest} =
   `"TEST " slot{'src1} `", " slot{'src2} hspace slot{'rest}

dform cmp_df : CMP{'src1; 'src2; 'rest} =
   `"CMP " slot{'src1} `", " slot{'src2} hspace slot{'rest}

dform jmp_df : JMP{'label; 'arg1} =
   `"JMP " slot{'label} `" /* args(" slot{'arg1} `") */"

dform jmp_df : JMP{'label; 'arg1; 'arg2} =
   `"JMP " slot{'label} `" /* args(" slot{'arg1} `"," slot{'arg2} `") */"

dform jmp_df : JMP{'label; 'arg1; 'arg2; 'arg3} =
   `"JMP " slot{'label} `" /* args(" slot{'arg1} `"," slot{'arg2} `"," slot{'arg3} `") */"

dform ijmp_df : IJMP{'src; 'arg1} =
   `"JMP *" slot{'src} `" /* args(" slot{'arg1} `") */"

dform ijmp_df : IJMP{'src; 'arg1; 'arg2} =
   `"JMP *" slot{'src} `" /* args(" slot{'arg1} `"," slot{'arg2} `") */"

dform ijmp_df : IJMP{'src; 'arg1; 'arg2; 'arg3} =
   `"JMP *" slot{'src} `" /* args(" slot{'arg1} `"," slot{'arg2} `"," slot{'arg3} `") */"

declare CC{'cc}

dform jcc_df : JCC{'cc; 'label; 'arg1; 'rest} =
   `"J" CC{'cc} `" " slot{'label} `" /* args(" slot{'arg1} `") */" hspace slot{'rest}

dform jcc_df : JCC{'cc; 'label; 'arg1; 'arg2; 'rest} =
   `"J" CC{'cc} `" " slot{'label} `" /* args(" slot{'arg1} `"," slot{'arg2} `") */" hspace slot{'rest}

dform jcc_df : JCC{'cc; 'label; 'arg1; 'arg2; 'arg3; 'rest} =
   `"J" CC{'cc} `" " slot{'label} `" /* args(" slot{'arg1} `"," slot{'arg2} `"," slot{'arg3} `") */" hspace slot{'rest}

dform set_eq_df : SET{'cc; 'label; 'rest} =
   `"SET" CC{'cc} `" " slot{'label} hspace slot{'rest}

dform cc_eq_df  : CC{EQ}  = `"Z"
dform cc_neq_df : CC{NEQ} = `"NZ"
dform cc_lt_df  : CC{LT}  = `"LT"
dform cc_le_df  : CC{LE}  = `"LE"
dform cc_gt_df  : CC{GT}  = `"GT"
dform cc_ge_df  : CC{GE}  = `"GE"
dform cc_ult_df : CC{ULT} = `"B"
dform cc_ule_df : CC{ULE} = `"BE"
dform cc_ugt_df : CC{UGT} = `"A"
dform cc_uge_df : CC{UGE} = `"AE"

dform comment_df : Comment[comment:s]{'rest} =
   `"/* Comment: " slot[comment:s] `" */" hspace slot{'rest}

(*
 * Programs.
 *)
dform label_fun_df : LabelFun{v. 'insts} =
   `"/* param " slot{'v} `" */" hspace slot{'insts}

dform label_rec_df : LabelRec{R1. 'fields; R2. 'rest} =
   szone `"/* LabelRecFields[" slot{'R1} `"] begins here */"
   hspace slot{'fields} hspace `"/* LabelRecFields[" slot{'R1} `"] ends here */" ezone
   hspace `"/* LabelRecBody[" slot{'R2} `"] begins here */" hspace slot{'rest}

dform label_def_df : LabelDef{'label; 'insts; 'rest} =
   szone pushm[3] slot{'label} hspace slot{'insts} popm ezone hspace slot{'rest}

dform label_end_df : LabelEnd =
   `""

dform label_asm_df : LabelAsm[label:t]{'R} =
   slot{'R} `"." slot[label:t] `":"

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
