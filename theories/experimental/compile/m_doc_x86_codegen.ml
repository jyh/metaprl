(* -*- mode: text; -*- *)
doc <:doc<
   @begin[spelling]
   env gc op tmp args vargs NZ
   @end[spelling]

   @subsection[m_doc_x86_codegen]{Assembly code generation}

   @docoff
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
extends M_doc_x86_asm

declare math_ASM{'e}
declare math_ASM{'a; 'v; 'e}
declare math_ASM{'a; 'v}

dform math_ASM_df1 : mode[tex] :: math_ASM{'e} =
   math_semleft slot{'e} math_subscript{math_semright; bf["a"]}

dform math_ASM_df2 : mode[tex] :: math_ASM{'a; 'v; 'e} =
   math_semleft slot{'a} math_subscript{math_semright; bf["a"]} slot{'v} `"." slot{'e}

dform math_ASM_df3 : mode[tex] :: math_ASM{'a; 'v} =
   math_semleft slot{'a} math_subscript{math_semright; bf["a"]} slot{'v} `"."

declare math_Reserve{'words; 'e}
declare math_StoreTuple{'p; 'i; 'args; 'e}
declare math_CopyArgs{'src; 'dst; 'v; 'e}

declare math_Reserve{'words}
declare math_StoreTuple{'p; 'i; 'args}
declare math_CopyArgs{'src; 'dst; 'v}
declare math_ReverseArgs{'src}

dform math_Reserve_df1 : mode[tex] :: math_Reserve{'words} =
   bf["reserve"] `"(" slot{'words} `")"

dform math_Reserve_df2 : mode[tex] :: math_Reserve{'words; 'e} =
   bf["reserve"] `"(" slot{'words} `");" slot{'e}

dform math_StoreTuple_df1 : mode[tex] :: math_StoreTuple{'p; 'i; 'args} =
   bf["store_tuple"] `"(" slot{'p} `"," slot{'i} `"," slot{'args} `");"

dform math_StoreTuple_df2 : mode[tex] :: math_StoreTuple{'p; 'i; 'args; 'e} =
   bf["store_tuple"] `"(" slot{'p} `"," slot{'i} `"," slot{'args} `");" slot{'e}

dform math_CopyArgs_df1 : mode[tex] :: math_CopyArgs{'src; 'dst; 'v} =
   bf["copy_args"] `"(" slot{'src} `"," slot{'dst} `")" math_dst{'v}

dform math_CopyArgs_df2 : mode[tex] :: math_CopyArgs{'src; 'dst; 'v; 'e} =
   bf["copy_args"] `"(" slot{'src} `"," slot{'dst} `")" math_dst{'v} slot{'e}

dform math_ReverseArgs_df1 : mode[tex] :: math_ReverseArgs{'e} =
   bf["reverse"] `"(" slot{'e} `")"

doc <:doc<


The production of assembly code is primarily a straightforward translation of operations in the
intermediate code to operations in the assembly.  There are two main kinds of translations:
translations from atoms to operands, and translation of expressions into instruction sequences.  We
express these translations with the term $@ASM{e}$, which is the translation of the IR expression
$e$ to an assembly expression; and $@ASM{a; v; e[v]}$, which produces the assembly operand for the atom
$a$ and substitutes it for the variable $v$ in assembly expression $e[v]$.

@subsubsection["asmatoms"]{Atom translation}

The translation of atoms is primarily a translation of the IR names for values and the assembly
names for operands.  A representative set of atom translations is shown in Figure
@reffigure[asmatomtrans].  As mentioned in Section @refsection[gc], we use a 31-bit representation
of integers, where the least-significant-bit is always set to 1.  The division operation is the most
complicated translation: first the operands $a_1$ and $a_2$ are shifted to obtain the standard
integer representation, the division operation is performed, and the result is converted to a 31-bit
representation.

@begin[figure,asmatomtrans]
$$
@begin[array,l]
@line{@xrewrite[false]{@ASM{@AtomFalse; v; e[v]}; e[@ImmediateNumber{1}]}}
@line{@xrewrite[true]{@ASM{@AtomTrue; v; e[v]}; e[@ImmediateNumber{3}]}}
@line{@xrewrite[int]{@ASM{@AtomInt[i]; v; e[v]}; e[@ImmediateNumber{i*2+1}]}}
@line{@xrewrite[var]{@ASM{@AtomVar{v_1}; v_2; e[v_2]}; e[@Register{v_1}]}}
@line{@xrewrite[label]{@ASM{@AtomFunVar{R; l}; v; e[v]}; e[@ImmediateCLabel{R; l}]}}
@line{{}}
@line{@xrewrite2[add]{@ASM{@AtomBinop{+; a_1; a_2}; v; e[v]};
   {@begin[array,t,l]
    @line{@ASM{a_1; v_1}}
    @line{@ASM{a_2; v_2}}
    @line{@Inst2Reg[ADD]{v_2; v_1; @it{tmp}}}
    @line{@Inst1Reg[DEC]{@Register{@it{tmp}}; @it{sum}}}
    @line{{e[@Register{@it{sum}}]}}
    @end[array]}}}
@line{{}}
@line{@xrewrite2[div]{@ASM{@AtomBinop{/; a_1; a_2}; v; e[v]};
   {@begin[array,t,l]
    @line{@ASM{a_1; v_1}}
    @line{@ASM{a_2; v_2}}
    @line{@Inst2Reg[SAR]{@ImmediateNumber{1}; v_1; v_1'}}
    @line{@Inst2Reg[SAR]{@ImmediateNumber{1}; v_2; v_2'}}
    @line{@Mov{@ImmediateNumber{0}; v_3}}
    @line{@Inst3Reg[DIV]{@Register{v_1'}; @Register{v_2'}; @Register{v_3'}; q'; r'}}
    @line{@Inst2Reg[SHL]{@ImmediateNumber{1}; @Register{q'}; q''}}
    @line{@Inst2Reg[OR]{@ImmediateNumber{1}; @Register{q''}; q}}
    @line{{e[@Register{q}]}}
    @end[array]}}}
@end[array]
$$
@caption{Translation of atoms to x86 assembly}
@end[figure]

@subsubsection["asmexps"]{Expression translation}

Expressions translate to sequences of assembly instructions.  A representative set of translations
in shown in Figure @reffigure[asmexptrans].  The translation of $@LetAtom{a; v; e[v]}$ is the
simplest case, the atom $a$ is translated into an operand $v'$, which is copied to a variable $v$
(since the expression $e[v]$ assumes $v$ is a variable), and the rest of the code $e[v]$ is
translated.  Conditionals translate into comparisons followed by a conditional branch.

@begin[figure,asmexptrans]
$$
@begin[array,l]
@line{@xrewrite2[atom]{@ASM{@LetAtom{a; v; e[v]}};
  {@begin[array,t,l]
   @line{@ASM{a; v'}}
   @line{@Mov{v'; v}}
   @line{@ASM{e[v]}}
   @end[array]}}}
@line{{}}
@line{@xrewrite2[if1]{@ASM{@If{a; e_1; e_2}};
  {@begin[array,t,l]
   @line{@ASM{a; @it{test}}}
   @line{@Cmp[CMP]{@ImmediateNumber{0}; @it{test}}}
   @line{@Jcc[J]{NZ; @ASM{e_1}; @ASM{e_2}}}
   @end[array]}}}
@line{{}}
@line{@xrewrite2[if2]{@ASM{@If{@AtomRelop{@it{op}; a_1; a_2}; e_1; e_2}};
  {@begin[array,t,l]
   @line{@ASM{a_1; v_1}}
   @line{@ASM{a_2; v_2}}
   @line{@Cmp[CMP]{v_1; v_2}}
   @line{@Jcc[J]{@ASM{@it{op}}; @ASM{e_1}; @ASM{e_2}}}
   @end[array]}}}
@line{{}}
@line{@xrewrite2[sub]{@ASM{@LetSubscript{a_1; a_2; v; e[v]}};
  {@begin[array,t,l]
   @line{@ASM{a_1; v_1}}
   @line{@ASM{a_2; v_2}}
   @line{@Mov{v_1; @it{tuple}}}
   @line{@Mov{v_2; @it{index}'}}
   @line{@Inst2Reg[SAR]{@ImmediateNumber{1}; @Register{@it{index}}'; @it{index}}}
   @line{@Mov{@MemRegOff{@it{tuple}; {-4}}; @it{size}'}}
   @line{@Inst2Reg[SAR]{@ImmediateNumber{2}; @Register{@it{size}'}; @it{size}}}
   @line{@Cmp[CMP]{@it{size}; @it{index}}}
   @line{@Jcc[J]{@it[AE]; @it{bounds.error}}}
   @line{@Mov{@MemRegRegOffMul{@it{tuple}; @it{index}; 0; 4}; v}}
   @line{@ASM{e[v]}}
   @end[array]}}}
@end[array]
$$
@caption{Translation of expressions to x86 assembly}
@end[figure]

The memory operations shown in Figure @reffigure[asmmemtrans] are among the most complicated
translations.  By convention, a pointer to a block points to the first field of the block (the word after
the header word).  The heap area itself is contiguous, delimited by $@it{base}$ and $@it{limit}$
pointers; the next allocation point is in the $@it{next}$ pointer.  These pointers are accessed
through the $@ContextRegister[name]$ pseudo-operand, which is later translated to an absolute memory
address.

@begin[figure,asmmemtrans]
$$
@begin[array,l]
@line{@xrewrite2[alloc]{@ASM{@LetTuple{@Length[i]; @it{tuple}; v; e[v]}};
   @begin[array,t,l]
   @line{@Reserve{@ImmediateNumber{|@it{tuple}|}}}
   @line{@Mov{@ContextRegister[next]; v}}
   @line{@Inst2Mem[ADD]{@ImmediateNumber{(|@it{tuple}|+1)*4}; @ContextRegister[next]}}
   @line{@Inst2Mem[MOV]{@ImmediateNumber{|@it{tuple}|*4}; @MemReg{v}}}
   @line{@Inst2Reg[ADD]{@ImmediateNumber{4}; @Register{v}; p}}
   @line{@StoreTuple{p; 0; @it{tuple}}}
   @line{@ASM{e[v]}}
   @end[array]}}
@line{{}}
@line{@xrewrite2[closure]{@ASM{@LetClosure{a_1; a_2; v; e[v]}};
   @begin[array,t,l]
   @line{@Reserve{@ImmediateNumber{3}}}
   @line{@Mov{@ContextRegister[next]; v}}
   @line{@Inst2Mem[ADD]{@ImmediateNumber{12}; @ContextRegister[next]}}
   @line{@Inst2Mem[MOV]{@ImmediateNumber{8}; @MemReg{v}}}
   @line{@ASM{a_1; v_1}}
   @line{@ASM{a_2; v_2}}
   @line{@Inst2Mem[MOV]{v_1; @MemRegOff{v; 4}}}
   @line{@Inst2Mem[MOV]{v_2; @MemRegOff{v; 8}}}
   @line{@Inst2Reg[ADD]{@ImmediateNumber{4}; @Register{v}; p}}
   @line{@ASM{e[p]}}
   @end[array]}}
@line{{}}
@line{@xrewrite2[call]{@ASM{@TailCall{'a; @it{args}}};
   @begin[array,t,l]
   @line{@ASM{a; @it{closure}}}
   @line{@Mov{@MemRegOff{@it{closure}; 4}; @it{env}}}
   @line{@CopyArgs{(); @it{args}; @it{vargs}}}
   @line{@Jmp[JMP]{@MemReg{@it{closure}}; @it{vargs}}}
   @end[array]}}
@end[array]
$$
@caption{Translation of memory operations to x86 assembly}
@end[figure]

The @tt{sub} rule shows the translation of an array subscripting operation.  Here the index is
compared against the number of words in the block as indicated in the header word, and a
bounds-check exception is raised if the index is out-of-bounds (denoted with the instruction
$@Jcc[J]{@it[AE]; @it{bounds.error}}$).  There is a similar rule for projecting values from
the tuples for closure environments, where the bounds-check may be omitted.

When a block of memory is allocated in the @misspelled{@tt{alloc}} and @misspelled{@tt{closure}}
rules, the first step reserves storage with the $@Reserve{i}$ term, and then the data is allocated
and initialized.  Figure @reffigure[asmhelp] shows the implementation of some of
the helper terms:
the $@Reserve{i}$ expression determines whether sufficient storage is present for an allocation of
$i$ bytes, and calls the garbage collector otherwise; the $@StoreTuple{p; i; @it{args}; e}$ term
generates the code to initialize the fields of a tuple from a set of arguments; and the
$@CopyArgs{@it{args}; @it{vargs}; v; e}$ term copies the argument list in $@it{@misspelled{args}}$
into registers.

@begin[figure,asmhelp]
$$
@begin[array,l]
@line{@xrewrite2[reserve]{@Reserve{i; e};
   @begin[array,t,l]
   @line{@Mov{@ContextRegister[limit]; @it{limit}}}
   @line{@Inst2Reg[SUB]{@ContextRegister[next]; @Register{@it{limit}}; @it{free}}}
   @line{@Cmp[CMP]{i; @Register{@it{free}}}}
   @line{@Jcc[J]{@CC["b"]; @it{gc}(i); e}}
   @end[array]}}
@line{{}}
@line{@xrewrite2[stuple1]{@StoreTuple{p; i; {(a :: @it{args})}; e};
   @begin[array,t,l]
   @line{@ASM{a; v}}
   @line{@Inst2Mem[MOV]{v; @MemRegOff{p; i}}}
   @line{@StoreTuple{p; i+4; @it{args}; e}}
   @end[array]}}
@line{{}}
@line{@xrewrite[stuple2]{@StoreTuple{p; i; (); e}; e}}
@line{{}}
@line{@xrewrite2[copy1]{@CopyArgs{{(a :: @it{args})}; @it{vargs}; v; e[v]};
   @begin[array,t,l]
   @line{@ASM{a; v'}}
   @line{@Mov{v'; v}}
   @line{@CopyArgs{@it{args}; {(@Register{v} :: @it{vargs})}; v; e[v]}}
   @end[array]}}
@line{{}}
@line{@xrewrite2[copy2]{@CopyArgs{(); @it{vargs}; v; e[v]}; e[@ReverseArgs{@it{vargs}}]}}
@end[array]
$$
@caption{Auxiliary terms for x86 code generation}
@end[figure]

@docoff

>>

(*
 * -*-
 * Local Variables:
 * fill-column: 100
 * End:
 * -*-
 *)
