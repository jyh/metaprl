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

(************************************************************************
 * Display forms.
 *)

(*
 * Operands.
 *)
dform immediate_number_df : ImmediateNumber[i:n] =
   `"#" slot[i:n]

dform immediate_label_df : ImmediateLabel[label:t]{'R} =
   slot{'R} `"." slot[label:t]

dform immediate_clabel_df : ImmediateCLabel[label:t]{'R} =
   `"$" slot{'R} `"." slot[label:t]

dform register_df : Register{'v} =
   `"%" slot{'v}

dform spill_register_df : SpillRegister{'v} =
   bf["spill["] slot{'v} bf["]"]

dform mem_reg_df : MemReg{'r} =
   `"(%" slot{'r} `")"

dform mem_reg_off_df : MemRegOff[i:n]{'r} =
   `"(%" slot{'r} `"," slot[i:n] `")"

dform mem_reg_reg_off_mul_df : MemRegRegOffMul[off:n, mul:n]{'r1; 'r2} =
   `"(%" slot{'r1} `",%" slot{'r2} `"," slot[off:n] `"," slot[mul:n] `")"

(*
 * Condition codes.
 *)
dform cc_df : CC[cc:s] =
   slot[cc:s]

(*
 * Instructions.
 *)
dform let_reg_df : Let{'src; dst. 'rest} =
    `"mov " slot{'src} `", %" slot{'dst} `" /* LET */" hspace slot{'rest}

dform inst1_df : Inst1[label:s]{'dst; 'rest} =
    slot[label:s] `" " slot{'dst} hspace slot{'rest}

dform inst2_df : Inst2[label:s]{'dst; 'src; 'rest} =
    slot[label:s] `" " slot{'src} `", " slot{'dst} hspace slot{'rest}

dform instm_df : Instm[label:s]{'dst1; 'dst2; 'src; 'rest} =
    slot[label:s] `" " slot{'src} `" /* dst(" slot{'dst1} `", " slot{'dst2} `" */" hspace slot{'rest}

dform shift_df : Shift[label:s]{'dst; 'src; 'rest} =
    slot[label:s] `" " slot{'src} `", " slot{'dst} hspace slot{'rest}

dform cmp_df : Cmp[opcode:s]{'src1; 'src2; 'rest} =
   slot[opcode:s] `" " slot{'src1} `", " slot{'src2} hspace slot{'rest}

dform set_df : Set[opcode:s]{'cc; 'dst; 'rest} =
   slot[opcode:s] 'cc `" " slot{'dst} hspace slot{'rest}

dform jmp_df : Jmp["jmp"]{'label; 'arg1} =
   `"jmp " slot{'label} `" /* args(" slot{'arg1} `") */"

dform jmp_df : Jmp["jmp"]{'label; 'arg1; 'arg2} =
   `"jmp " slot{'label} `" /* args(" slot{'arg1} `", " slot{'arg2} `") */"

dform jmp_df : Jmp["jmp"]{'label; 'arg1; 'arg2; 'arg3} =
   `"jmp " slot{'label} `" /* args(" slot{'arg1} `", " slot{'arg2} `", " slot{'arg3} `") */"

dform ijmp_df : Jmp["ijmp"]{'src; 'arg1} =
   `"jmp *" slot{'src} `" /* args(" slot{'arg1} `") */"

dform ijmp_df : Jmp["ijmp"]{'src; 'arg1; 'arg2} =
   `"jmp *" slot{'src} `" /* args(" slot{'arg1} `", " slot{'arg2} `") */"

dform ijmp_df : Jmp["ijmp"]{'src; 'arg1; 'arg2; 'arg3} =
   `"jmp *" slot{'src} `" /* args(" slot{'arg1} `", " slot{'arg2} `", " slot{'arg3} `") */"

dform jcc_df : Jcc["jcc"]{'cc; 'label; 'arg1; 'rest} =
   `"j" 'cc `" " slot{'label} `" /* args(" slot{'arg1} `") */" hspace slot{'rest}

dform jcc_df : Jcc["jcc"]{'cc; 'label; 'arg1; 'arg2; 'rest} =
   `"j" 'cc `" " slot{'label} `" /* args(" slot{'arg1} `", " slot{'arg2} `") */" hspace slot{'rest}

dform jcc_df : Jcc["jcc"]{'cc; 'label; 'arg1; 'arg2; 'arg3; 'rest} =
   `"j" 'cc `" " slot{'label} `" /* args(" slot{'arg1} `", " slot{'arg2} `", " slot{'arg3} `") */" hspace slot{'rest}

(*
 * Comments.
 *)
dform comment_df : Comment[comment:s]{'rest} =
   `"/* Comment: " slot[comment:s] `" */" hspace slot{'rest}

(*
 * Programs.
 *)
dform label_fun_df : LabelFun{v. 'insts} =
   `"/* param " slot{'v} `" */" hspace slot{'insts}

dform label_rec_df : LabelRec{R1. 'fields; R2. 'rest} =
   szone `"/* LabelRecFields[" slot{'R1} `"] begins here */"
   hspace slot{'fields} `"/* LabelRecFields[" slot{'R1} `"] ends here */" ezone
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
