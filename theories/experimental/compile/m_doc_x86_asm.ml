doc <:doc< -*- mode: text; -*-
   @begin[spelling]
   mem reg
   @end[spelling]
  
   @begin[doc]
   @section[m_doc_x86_asm]{Scoped x86 assembly language}
   @docoff
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
   Copyright (C) 2003 Jason Hickey, Caltech
  
   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.
  
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
  
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
  
   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]
>>
extends M_doc_ir

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

(*
 * Display dst as binding occurrence.
 *)
declare math_dst{'dst}
declare math_dst{'dst1; 'dst2}

(*
 * Display forms.
 *)
dform math_dst_df1 : mode[tex] :: math_dst{'dst} =
   lambda slot{'dst} `"."

dform math_dst_df2 : mode[tex] :: math_dst{'dst1; 'dst2} =
   lambda slot{'dst1} `"," slot{'dst2} `"."

(*
 * Operands.
 *)
dform immediate_number_df : mode[tex] :: math_ImmediateNumber{'i} =
   `"$" slot{'i}

dform immediate_label_df : mode[tex] :: math_ImmediateLabel{'R; 'label} =
   slot{'R} `"." slot{'label}

dform immediate_clabel_df : mode[tex] :: math_ImmediateCLabel{'R; 'label} =
   `"$" slot{'R} `"." slot{'label}

dform register_df : mode[tex] :: math_Register{'v} =
   `"%" slot{'v}

dform spill_memory_df : mode[tex] :: math_SpillMemory{'spill} =
   bf["spill["] slot{'spill} bf["]"]

dform spill_register_df : mode[tex] :: math_SpillRegister{'v; 'spill} =
   bf["spill["] slot{'v} bf[", "] slot{'spill} bf["]"]

dform context_register_df : mode[tex] :: math_ContextRegister[name:s] =
   bf["context["] slot[name:s] bf["]"]

dform mem_reg_df : mode[tex] :: math_MemReg{'r} =
   `"(%" slot{'r} `")"

dform mem_reg_off_df : mode[tex] :: math_MemRegOff{'r; 'off} =
   slot{'off} `"(%" slot{'r} `")"

dform mem_reg_reg_off_mul_df : mode[tex] :: math_MemRegRegOffMul{'r1; 'r2; 'off; 'mul} =
   slot{'off} `"(%" slot{'r1} `",%" slot{'r2} `"," slot{'mul} `")"

(*
 * Condition codes.
 *)
dform cc_df : mode[tex] :: math_CC[cc:s] =
   bf{slot[cc:s]}

(*
 * Instructions.
 *)
dform mov_df1 : mode[tex] :: math_Mov{'src; 'dst} =
    math_it["MOV "] slot{'src} bf[", "] math_dst{'dst}

dform mov_df2 : mode[tex] :: math_Mov{'src; 'dst; 'rest} =
    math_it["MOV "] slot{'src} bf[", "] math_dst{'dst} slot{'rest}

dform set_spill_df1 : mode[tex] :: math_Spill["set"]{'src; 'dst} =
    math_it["SPILL "] slot{'src} bf[", "] math_dst{'dst}

dform set_spill_df2 : mode[tex] :: math_Spill["set"]{'src; 'dst; 'rest} =
    math_it["SPILL "] slot{'src} bf[", "] math_dst{'dst} slot{'rest}

dform get_spill_df1 : mode[tex] :: math_Spill["get"]{'src; 'dst} =
    math_it["SPILL "] slot{'src} bf[", "] math_dst{'dst}

dform get_spill_df2 : mode[tex] :: math_Spill["get"]{'src; 'dst; 'rest} =
    math_it["SPILL "] slot{'src} bf[", "] math_dst{'dst} slot{'rest}

dform copy_spill_df1 : mode[tex] :: math_Spill["copy"]{'src; 'dst} =
    math_it["SPILL "] slot{'src} bf[", "] math_dst{'dst}

dform copy_spill_df2 : mode[tex] :: math_Spill["copy"]{'src; 'dst; 'rest} =
    math_it["SPILL "] slot{'src} bf[", "] math_dst{'dst} slot{'rest}

dform inst1_mem_df1 : mode[tex] :: math_Inst1Mem[opcode:s]{'dst} =
    math_it[opcode:s] `" " slot{'dst}

dform inst1_mem_df2 : mode[tex] :: math_Inst1Mem[opcode:s]{'dst; 'rest} =
    math_it[opcode:s] `" " slot{'dst} `";" slot{'rest}

dform inst1_reg_df1 : mode[tex] :: math_Inst1Reg[opcode:s]{'src; 'dst} =
    math_it[opcode:s] `" " slot{'src} bf[", "] math_dst{'dst}

dform inst1_reg_df2 : mode[tex] :: math_Inst1Reg[opcode:s]{'src; 'dst; 'rest} =
    math_it[opcode:s] `" " slot{'src} bf[", "] math_dst{'dst} slot{'rest}

dform inst2_mem_df1 : mode[tex] :: math_Inst2Mem[opcode:s]{'src; 'dst} =
    math_it[opcode:s] `" " slot{'src} bf[", "] slot{'dst}

dform inst2_mem_df2 : mode[tex] :: math_Inst2Mem[opcode:s]{'src; 'dst; 'rest} =
    math_it[opcode:s] `" " slot{'src} bf[", "] slot{'dst} `";" slot{'rest}

dform inst2_reg_df1 : mode[tex] :: math_Inst2Reg[opcode:s]{'src1; 'src2; 'dst} =
    math_it[opcode:s] `" " slot{'src1} bf[", "] slot{'src2} bf[", "] math_dst{'dst}

dform inst2_reg_df2 : mode[tex] :: math_Inst2Reg[opcode:s]{'src1; 'src2; 'dst; 'rest} =
    math_it[opcode:s] `" " slot{'src1} bf[", "] slot{'src2} bf[", "] math_dst{'dst} slot{'rest}

dform inst3_reg_df1 : mode[tex] :: math_Inst3Reg[opcode:s]{'src1; 'src2; 'src3; 'dst2; 'dst3} =
    math_it[opcode:s] `" " slot{'src1} bf[", "] slot{'src2} bf[", "] slot{'src3} bf[", "] math_dst{'dst2; 'dst3}

dform inst3_reg_df1 : mode[tex] :: math_Inst3Reg[opcode:s]{'src1; 'src2; 'src3; 'dst2; 'dst3; 'rest} =
    math_it[opcode:s] `" " slot{'src1} bf[", "] slot{'src2} bf[", "] slot{'src3} bf[", "] math_dst{'dst2; 'dst3} slot{'rest}

dform shift_mem_df1 : mode[tex] :: math_ShiftMem[opcode:s]{'src; 'dst} =
    math_it[opcode:s] `" " slot{'src} bf[", "] slot{'dst}

dform shift_mem_df2 : mode[tex] :: math_ShiftMem[opcode:s]{'src; 'dst; 'rest} =
    math_it[opcode:s] `" " slot{'src} bf[", "] slot{'dst} `";" slot{'rest}

dform shift_reg_df1 : mode[tex] :: math_ShiftReg[opcode:s]{'src1; 'src2; 'dst} =
    math_it[opcode:s] `" " slot{'src1} bf[", "] slot{'src2} bf[", "] math_dst{'dst}

dform shift_reg_df2 : mode[tex] :: math_ShiftReg[opcode:s]{'src1; 'src2; 'dst; 'rest} =
    math_it[opcode:s] `" " slot{'src1} bf[", "] slot{'src2} bf[", "] math_dst{'dst} slot{'rest}

dform cmp_df1 : mode[tex] :: math_Cmp[opcode:s]{'src1; 'src2} =
   math_it[opcode:s] `" " slot{'src1} bf[", "] slot{'src2}

dform cmp_df2 : mode[tex] :: math_Cmp[opcode:s]{'src1; 'src2; 'rest} =
   math_it[opcode:s] `" " slot{'src1} bf[", "] slot{'src2} `";" slot{'rest}

dform set_reg_df1 : mode[tex] :: math_SetReg[opcode:s]{'cc; 'src; 'dst} =
   math_it[opcode:s] 'cc `" " slot{'src} bf[", "] math_dst{'dst}

dform set_reg_df2 : mode[tex] :: math_SetReg[opcode:s]{'cc; 'src; 'dst; 'rest} =
   math_it[opcode:s] 'cc `" " slot{'src} bf[", "] math_dst{'dst} slot{'rest}

dform set_mem_df1 : mode[tex] :: math_SetMem[opcode:s]{'cc; 'dst} =
   math_it[opcode:s] 'cc `" " slot{'dst}

dform set_mem_df2 : mode[tex] :: math_SetMem[opcode:s]{'cc; 'dst; 'rest} =
   math_it[opcode:s] 'cc `" " slot{'dst} `";" slot{'rest}

dform jmp_df : mode[tex] :: math_Jmp[opcode:s]{'src; 'args} =
   math_it[opcode:s] `" " slot{'src} bf["("] slot{'args} bf[")"]

dform jcc_df1 : mode[tex] :: math_Jcc[opcode:s]{'cc; 'rest1} =
   math_it[opcode:s] 'cc math_xthen slot{'rest1} math_xelse

dform jcc_df2 : mode[tex] :: math_Jcc[opcode:s]{'cc; 'rest1; 'rest2} =
   math_it[opcode:s] 'cc math_xthen slot{'rest1} math_xelse slot{'rest2}

(*
 * Reserve.
 *)
dform asm_reserve_df1 : mode[tex] :: math_AsmReserve{'words} =
   bf["reserve"] `"(" slot{'words} `")"

dform asm_reserve_df2 : mode[tex] :: math_AsmReserve{'words; 'e} =
   bf["reserve"] `"(" slot{'words} `");" slot{'e}

(*
 * Comments.
 *)
dform comment_df : mode[tex] :: math_Comment{'comment; 'rest} =
   `"/* Comment: mode[tex] :: math_" slot{'comment} `" */" slot{'rest}

dform init_df : mode[tex] :: math_Init{'rest} =
   szone pushm[0] pushm[3] bf["initialize"]
   slot{'rest}
   popm hspace
   bf["end"]
   popm ezone

(*
 * Programs.
 *)
dform label_fun_df : mode[tex] :: math_LabelFun{'v; 'insts} =
   lambda slot{'v} `"." slot{'insts}

dform math_LabelRec_df : mode[tex] :: math_LabelRec{'R; 'e1; 'e2} =
   math_xlet math_bf[" rec "] slot{'R} `"=" slot{'e1} math_xin slot{'e2}

dform label_def_df : mode[tex] :: math_LabelDef{'label; 'insts; 'rest} =
   slot{'label} `"=" slot{'insts} bf[" and "] slot{'rest}

dform label_end_df : mode[tex] :: math_LabelEnd =
   epsilon

dform label_asm_df : mode[tex] :: math_LabelAsm{'R; 'label} =
   slot{'R} `"." slot{'label} `":"

doc <:doc< 

@begin[doc]

Once closure conversion has been performed, all function definitions are top-level and closed, and
it becomes possible to generate assembly code.  When formalizing the assembly code, we continue to
use higher-order abstract syntax: registers and variables in the assembly code correspond to
variables in the meta-language.  There are two important properties we must maintain.  First,
scoping must be preserved: there must be a binding occurrence for each variable that is used.
Second, in order to facilitate reasoning about the code, variables/registers must be immutable.

These two requirements seem at odds with the traditional view of assembly, where assembly
instructions operate by side-effect on a finite register set.  In addition, the Intel x86
instruction set architecture primarily uses two-operand instructions, where the value in one operand
is both used and modified in the same instruction.  For example, the instruction @it{ADD
$r_1$,$r_2$} performs the operation $r_1 @leftarrow r_1 + r_2$, where $r_1$ and $r_2$ are registers.

To address these issues, we define an abstract version of the assembly language that uses a three
operand version on the instruction set.  The instruction $@Inst2Reg[ADD]{v_1; v_2; v_3; e}$ performs the
abstract operation $@xlet v_3 = v_1 + v_2 @xin e$.  The variable $v_3$ is a @emph{binding} occurrence,
and it is bound in body of the instruction $e$.  In our account of the instruction set, @em{every}
instruction that modifies a register has a binding occurrence of the variable being modified.
Instructions that @em{do not} modify registers use the traditional non-binding form of the instruction.
For example, the instruction $@Inst2Mem[ADD]{v_1; @MemReg{v_2}; e}$ performs the operation $@MemReg{v_2}
@leftarrow @MemReg{v_2} + v_1$, where $@MemReg{v_2}$ means the value in memory at location $v_2$.

@begin[figure,isa]
$$
@begin[array,rcll]
@line{l       {::=}   @it{string}                                                   @hbox{Function labels}}
@line{@it{r}  {::=}   {@it{eax} {@pipe} @it{ebx} {@pipe} @it{ecx} {@pipe} @it{edx}} @hbox{Registers}}
@line{{}      {@pipe} {@it{esi} {@pipe} @it{edi} {@pipe} @it{esp} {@pipe} @it{ebp}} {}}
@line{@it{v}  {::=}   {r {@pipe} v_1, v_2, @ldots}                                  @hbox{Variables}}
@line{{} {} {} {}}
@line{o_m     {::=}   @MemReg{v}                                                    @hbox{Memory operands}}
@line{{}      {@pipe} @MemRegOff{v; i}                                              {}}
@line{{}      {@pipe} @MemRegRegOffMul{v_1; v_2; i_1; i_2}                          {}}
@line{o_r     {::=}   @Register{v}                                                  @hbox{Register operand}}
@line{@it{o}  {::=}   {o_m @pipe o_r}                                               @hbox{General operands}}
@line{{}      {@pipe} @ImmediateNumber{i}                                           @hbox{Constant number}}
@line{{}      {@pipe} @ImmediateCLabel{v; l}                                        @hbox{Label}}
@line{{} {} {} {}}
@line{@it{cc} {::=}   {= {@pipe} <> {@pipe} < {@pipe} > {@pipe} {@le} {@pipe} @ge}  @hbox{Condition codes}}
@line{@it{inst1} {::=}   {@it{INC} @pipe @it{DEC} @pipe @cdots}                     @hbox{1-operand opcodes}}
@line{@it{inst2} {::=}   {@it{ADD} @pipe @it{SUB} @pipe @it{AND} @pipe @cdots}      @hbox{2-operand opcodes}}
@line{@it{inst3} {::=}   {@it{MUL} @pipe @it{DIV}}                                  @hbox{3-operand opcodes}}
@line{@it{cmp}   {::=}   {@it{CMP} @pipe @it{TEST}}                                 @hbox{comparisons}}
@line{@it{jmp}   {::=}   {@it{JMP}}                                                 @hbox{unconditional branch}}
@line{@it{jcc}   {::=}   {@it{JEQ} @pipe @it{JLT} @pipe @it{JGT} @pipe @cdots}      @hbox{conditional branch}}
@line{@it{e}  {::=}   @Mov{o; v; e}                                                 @hbox{Copy}}
@line{{}      {@pipe} @Inst1Mem[inst1]{o_m; e}                                      @hbox{1-operand mem inst}}
@line{{}      {@pipe} @Inst1Reg[inst1]{o_r; v; e}                                   @hbox{1-operand reg inst}}
@line{{}      {@pipe} @Inst2Mem[inst2]{o_r; o_m; e}                                 @hbox{2-operand mem inst}}
@line{{}      {@pipe} @Inst2Reg[inst2]{o; o_r; v; e}                                @hbox{2-operand reg inst}}
@line{{}      {@pipe} @Inst3Reg[inst3]{o; o_r; o_r; v_1; v_2; e}                    @hbox{3-operand reg inst}}
@line{{}      {@pipe} @Cmp[cmp]{o_1; o_2}                                           @hbox{Comparison}}
@line{{}      {@pipe} @Jmp[jmp]{o; {o_r; @ldots; o_r}}                              @hbox{Unconditional branch}}
@line{{}      {@pipe} @Jcc[j]{@it{cc}; e_1; e_2}                                    @hbox{Conditional branch}}
@line{{} {} {} {}}
@line{p       {@pipe} {@LabelRec{R; d; p} {@pipe} e}                                @hbox{Programs}}
@line{d       {@pipe} {@LabelDef{l; e_@lambda; d} {@pipe} @LabelEnd}                @hbox{Function definition}}
@line{{e_@lambda} {::=} {@LabelFun{v; e_@lambda} @pipe e}                           @hbox{Functions}}
@end[array]
$$
@caption{Scoped Intel x86 instruction set}
@end[figure]

The complete abstract instruction set that we use is shown in Figure @reffigure[isa] (the Intel x86
architecture includes a large number of complex instructions that we do not use).  Instructions may
use several forms of operands and addressing modes.

@begin[itemize]
@item{{The @em{immediate} operand $@ImmediateNumber{i}$ is a constant number $i$.}}
@item{{The @em{label} operand $@ImmediateCLabel{R; l}$ refers to the address of the function in record $R$ labeled $l$.}}
@item{{The @em{register} operand $@Register{v}$ refers to register/variable $v$.}}
@item{{The @em{indirect} operand $@MemReg{v}$ refers to the value in memory at location $v$.}}
@item{{The @em{indirect offset} operand $@MemRegOff{v; i}$ refers to the value in memory at location $v+i$.}}

@item{{The @em{array indexing} operand $@MemRegRegOffMul{v_1; v_2; i_1; i_2}$ refers to the value in
memory at location $v_1 + v_2 * i_2 + i_1$, where $i_2 @in @lbrace 1, 2, 4, 8 @rbrace$.}}

@end[itemize]

The instructions can be placed in several main categories.

@begin[itemize]

@item{{@it{MOV} instructions copy a value from one location to another.  The instruction $@Mov{o_1;
v_2; e[v_2]}$ copies the value in operand $o_1$ to variable $v_2$.}}

@item{{One-operand instructions have the forms $@Inst1Mem[inst1]{o_1; e}$ (where $o_1$ must be
an indirect operand), and $@Inst1Reg[inst1]{v_1; v_2; e}$.  For example, the instruction
$@Inst1Mem[INC]{@MemReg{r_1}; e}$ performs the operation $@MemReg{r_1} @leftarrow @MemReg{r_1} + 1;
e$; and the instruction $@Inst1Reg[INC]{@Register{r_1}; r_2; e}$ performs the operation $@xlet r_2 =
r_1 + 1 @xin e$.}}

@item{{Two-operand instructions have the forms $@Inst2Mem[inst2]{o_1; o_2; e}$, where $o_2$ must be
an indirect operand; and $@Inst2Reg[inst2]{o_1; v_2; v_3; e}$.  For example, the instruction
$@Inst2Mem[ADD]{@Register{r_1}; @MemReg{r_2}; e}$ performs the operation $@MemReg{r_2} @leftarrow
@MemReg{r_2} + r_1; e$; and the instruction $@Inst2Reg[ADD]{o_1; v_2; v_3; e}$ is equivalent to $@xlet v_3
= o_1 + v_2 @xin e$.}}

@item{{There are two three-operand instructions: one for multiplication and one for division, having
the form $@Inst3Reg[inst3]{o_1; v_2; v_3; v_4; v_5; e}$.  For example, the instruction
$@Inst3Reg[DIV]{@Register{r_1}; @Register{r_2}; @Register{r_3}; r_4; r_5; e}$ performs the following
operation, where $(r_2, r_3)$ is the 64-bit value $r_2 * 2^32 + r_3$.  The Intel specification
requires that $r_4$ be the register $@it{eax}$, and $r_5$ the register $@it{edx}$.

$$
@begin[array,l]
@line{{@xlet r_4 = (r_2, r_3) / r_1 @xin}}
@line{{@xlet r_5 = (r_2, r_3) @mathrel{@bf[mod]} r_1 @xin}}
@line{{@quad e}}
@end[array]
$$}}

@item{{The comparison operand has the form $@Cmp[CMP]{o_1; o_2; e}$, where the processor's
condition code register is modified by the instruction.  We do not model the condition code register
explicitly in our current account.  However, doing so would allow more greater flexibility during
code-motion optimizations on the assembly.}}

@item{{The unconditional branch operation $@Jmp[JMP]{o; {o_1, @ldots, o_n}}$ branches to the
function specified by operand $o$, with arguments $(o_1, @ldots, o_n)$.  The arguments are provided
so that the calling convention may be enforced.}}

@item{{The conditional branch operation $@Jcc[J]{@it{cc}; e_1; e_2}$ is a conditional.  If the
condition-code matches the value in the processor's condition-code register, then the instruction
branches to expression $e_1$; otherwise it branches to expression $e_2$.}}

@item{{Functions are defined using the $@LabelRec{R; d; e}$ which corresponds exactly to the
same expression in the intermediate representation.  The subterm $d$ is a list of
function definitions, and $e$ is an assembly program.  Functions are defined with the $@LabelFun{v;
e}$, where $v$ is a function parameter in instruction sequence $e$.}}

@end[itemize]

@subsection[concreteasm]{Translation to concrete assembly}

Since the instruction set as defined is abstract, and contains binding structure, it must be
translated before actual generation of machine code.  The first step in doing this is register
allocation: every variable in the assembly program must be assigned to an actual machine register.
This step corresponds to an $@alpha$-conversion where variables are renamed to be the names of
actual registers; the formal system merely validates the renaming.  We describe this phase in the
section on register allocation @refsection[m_doc_x86_regalloc].

The final step is to generate the actual program from the abstract program.  This requires only
local modifications, and is implemented during printing of the program (that is, it is implemented
when the program is exported to an external assembler).  The main translation is as follows.

@begin[itemize]

@item{{Memory instructions $@Inst1Mem[inst1]{o_m; e}$, $@Inst2Mem[inst2]{o_r; o_m; e}$, and
$@Cmp[cmp]{o_1; o_2; e}$ can be printed directly.}}

@item{{Register instructions with binding occurrences require a possible additional $@it{mov}$
instruction.  For the 1-operand instruction $@Inst1Reg[inst1]{o_r; r; e}$, if $o_r = @Register{r}$,
then the instruction is implemented as $@it{inst1}@quad r$.  Otherwise, it is implemented as the
two-instruction sequence:

@begin[center]
@begin[tabular,ll]
@line{{MOV} {$o_r,%r$}}
@line{{inst1} {$%r$}}
@end[tabular]
@end[center]

Similarly, the two-operand instruction $@Inst2Reg[inst2]{o; o_r; r; e}$ may require an additional @tt[mov]
from $o_r$ to $r$, and the three-operand instruction $@Inst3Reg[inst3]{o; o_r_1; o_r_2; r_1; r_2; e}$ may
require two additional @tt{mov} instructions.}}

@item{{The $@Jmp[JMP]{o; {o_1, @ldots, o_n}}$ prints as @tt{JMP o}.  This assumes that the calling
convention has been satisfied during register allocation, and all the arguments are in the
appropriate places.}}

@item{{The $@Jcc[J]{@it{cc}; e_1; e_2}$ instruction prints as the following sequence, where
$@it{cc}'$ is the inverse of $@it{cc}$, and $l$ is a new label.

@begin[center]
@begin[tabular,ll]
@line{{J$@it{cc}'$} {l}}
@line{{} {$e_1$}}
@line{{l:} {$e_2$}}
@end[tabular]
@end[center]}}

@item{{A function definition $@LabelDef{l; e; d}$ in a record $@LabelRec{R; d; e}$ is implemented as
a labeled assembly expression $R.l@colon e$.  We assume that the calling convention has been
established, and the function abstraction $@LabelFun{v; e}$ ignores the parameter $v$, assembling
only the program $e$.}}

@end[itemize]

The compiler back-end then has three stages: 1) code generation, 2) register allocation, and 3)
peephole optimization, described in the following sections.

@docoff
@end[doc]

>>

(*
 * -*-
 * Local Variables:
 * fill-column: 100
 * End:
 * -*-
 *)
