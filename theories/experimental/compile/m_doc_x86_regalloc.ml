doc <:doc< -*- mode: text; -*-
   @begin[spelling]
   Chaitin NP
   @end[spelling]

   @begin[doc]
   @subsection[m_doc_x86_regalloc]{Register allocation}
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
extends M_doc_x86_asm

doc <:doc<

@begin[doc]

Register allocation is one of the easier phases of the compiler formally: the main objective of
register allocation is to rename the variables in the program to use register names.  Because we are using higher-order abstract syntax, the formal
problem is just an $@alpha$-conversion, which can be checked readily by the formal system.  From a
practical standpoint, however, register allocation is a NP-complete problem, and the majority of the
code in our implementation is devoted to a Chaitin-style @cite["CACC+81"] graph-coloring register
allocator.  These kinds of allocators have been well-studied, and we do not discuss the details of
the allocator here.  The overall structure of the register allocator algorithm is as follows.

@begin[enumerate]

@item{Given a program $p$, run a register allocator $R(p)$.}

@item{{If the register allocator $R(p)$ was successful, it returns an assignment of variables to register
names; $@alpha$-convert the program using this variable assignment, and return the result $p'$.}}

@item{{Otherwise, if the register allocator $R(p)$ was not successful, it returns a set of variables
to ``spill'' into memory.  Rewrite the program to add fetch/store code for the spilled registers,
generating a new program $p'$, and run register allocation $R(p')$ on the new program.}}

@end[enumerate]

Part 2 is a trivial formal operation (the logical framework checks that $p' = p$).  The generation
of spill code for part 3 is not trivial however, as we discuss in the following section.

@subsection[spilling]{Generation of spill code}

The generation of spill code can affect the performance of a program dramatically, and it is
important to minimize the amount of memory traffic.  Suppose the register allocator was not able to
generate a register assignment for a program $p$, and instead it determines that variable $v$ must
be placed in memory.  We can allocate a new global variable, say $@it{spill}_i$ for this purpose,
and replace all occurrences of the variable with a reference to the new memory location.  This can
be captured by rewriting the program just after the binding occurrences of the variables to be
spilled.  The following two rules give an example.
$$
@begin[array,l]
@line{@xrewrite["smov"]{@Mov{o; v; e[v]}; @Mov{o; @it{spill}_i; e[@it{spill}_i]}}}
@line{@xrewrite2["sinst2"]{@Inst2Reg[inst2]{o; o_r; v; e[v]};
   @begin[array,t,l]
   @line{@Mov{o_r; @it{spill}_i}}
   @line{@Inst2Mem[inst2]{o; @it{spill}_i}}
   @line{{e[@it{spill}_i]}}
   @end[array]}}
@end[array]
$$
However, this kind of brute-force approach spills @em{all} of the occurrences of the variable, even
those occurrences that could have been assigned to a register.  Furthermore, the spill location
$@it{spill}_i$ would presumably be represented as the label of a memory location, not a variable,
allowing a conflicting assignment of another variable to the same spill location.

To address both of these concerns, we treat spill locations as variables, and introduce scoping for
spill variables.  We introduce two new pseudo-operands, and two new instructions, shown in Figure
@reffigure[spilling].  The instruction $@Spill[set]{o_r; s; e[s]}$ generates a new
spill location
represented in the variable $s$, and stores the operand $o_r$ in that spill location.  The operand
$@SpillRegister{v; s}$ represents the value in spill location $s$, and it also specifies that the
values in spill location $s$ and in the register $v$ are the same.  The operand $@SpillMemory{s}$
refers the the value in spill location $s$.  The value in a spill operand is retrieved with the
$@Spill[get]{o_s; v; e[v]}$ and placed in the variable $v$.

@begin[figure,spilling]
$$
@begin[array,rcll]
@line{{o_s} {::=}   {@SpillRegister{v; s}}      @hbox{Spill operands}}
@line{{}    {@pipe} {@SpillMemory{s}}           {}}
@line{{} {} {} {}}
@line{{e}   {::=}   {@Spill[set]{o_r; s; e[s]}} @hbox{New spill}}
@line{{}    {@pipe} {@Spill[get]{o_s; v; e[v]}} @hbox{Get the spilled value}}
@end[array]
$$
@caption{Spill pseudo-operands and instructions}
@end[figure]

The actual generation of spill code then proceeds in two main phases.  Given a variable to spill,
the first phase generates the code to store the value in a new spill location, then adds copy
instruction to split the live range of the variable so that all uses of the variable refer to
different freshly-generated operands of the form $@SpillRegister{v; s}$.  For example, consider the
code fragment shown in Figure @reffigure[spillex], and suppose the register allocator
determines that the variable $v$ is to be spilled, because a register cannot be assigned in code
segment 2.

@begin[figure,spillex]
$$
@begin[array,ccc]
@line{{
@begin[array,l]
@line{@Inst2Reg[AND]{o; o_r; v}}
@line{@hbox{...code segment 1...}}
@line{@Inst2Mem[ADD]{@Register{v}; o}}
@line{@hbox{...code segment 2...}}
@line{@Inst2Mem[SUB]{@Register{v}; o}}
@line{@hbox{...code segment 3...}}
@line{@Inst2Mem[OR]{@Register{v}; o}}
@end[array]}
{@tt["   "]@longrightarrow@tt["   "]}
{@begin[array,l]
@line{@Inst2Reg[AND]{o; o_r; v_1}}
@line{@Spill[set]{@Register{v_1}; s}}
@line{@hbox{...code segment 1...}}
@line{@Spill[get]{@SpillRegister{v_1; s}; v_2}}
@line{@Inst2Mem[ADD]{@Register{v_2}; o}}
@line{@hbox{...code segment 2...}}
@line{@Spill[get]{@SpillRegister{v_2; s}; v_3}}
@line{@Inst2Mem[SUB]{@Register{v_3}; o}}
@line{@hbox{...code segment 3...}}
@line{@Spill[get]{@SpillRegister{v_3; s}; v_4}}
@line{@Inst2Mem[OR]{@Register{v}; o}}
@end[array]}}
@end[array]
$$
@caption{Spill example}
@end[figure]

The first phase rewrites the code as follows.  The initial occurrence of the variable is spilled
into a new spill location $s$.  The value is fetched just before each use of the variable, and
copied to a new register, as shown in Figure @reffigure[spillex].  Note that the later
uses refer to the new registers, creating a copying daisy-chain, but the registers have not been
actually eliminated.

Once the live range is split, the register allocator has the freedom to spill only part of the live
range.  During the second phase of spilling, the allocator will determine that register $v_2$ must
be spilled in code segment 2, and the $@SpillRegister{v_2; s}$ operand is replaced with
$@SpillMemory{s}$ forcing the fetch from memory, not the register $v_2$.  Register $v_2$ is no
longer live in code segment 2, easing the allocation task without also spilling the register in code
segments 1 and 3.

@subsection[formalspilling]{Formalizing spill code generation}

The formalization of spill code generation can be performed in three parts.  The first part
generates new spill locations (line 2 in the code sequence above); the second part generates
live-range splitting code (lines 4, 7, and 10); and the third part replaces operands of the form
$@SpillRegister{v; s}$ with $@SpillMemory{s}$ when requested by the register allocator.

The first part requires a rewrite for each kind of instruction that contains a binding occurrence of
a variable.  The following two rewrites are representative examples.  Note that all occurrences of
the variable $v$ are replaced with $@SpillRegister{v; s}$, potentially generating operands like
$@MemRegOff{@SpillRegister{v; s}; i}$.  These kinds of operands are rewritten at the end of
spill-code generation to their original form, e.g. $@MemRegOff{v; i}$.
$$
@begin[array,l]
@line{@xrewrite2["smov"]{@Mov{o_r; v; e[v]};
   @begin[array,t,l]
   @line{@Mov{o_r; v}}
   @line{@Spill[set]{@Register{v}; s}}
   @line{{e[@SpillRegister{v; s}]}}
   @end[array]}}
@line{@xrewrite2["sinst2"]{@Inst2Reg[inst2]{o; o_r; v; e[v]};
   @begin[array,t,l]
   @line{@Inst2Reg[inst2]{o; o_r; v; e[v]}}
   @line{@Spill[set]{@Register{v}; s}}
   @line{{e[@SpillRegister{v; s}]}}
   @end[array]}}
@end[array]
$$

The second rewrite splits a live range of a spill at an arbitrary point.  This rewrite applies to
any program that contains an occurrence of an operand $@SpillRegister{v_1; s}$, and translates it to
a new program that fetches the spill into a new register $v_2$ and uses the new spill operand
$@SpillRegister{v_2; s}$ in the remainder of the program.  This rewrite is selectively applied
before any instruction that uses an operand $@SpillRegister{v_1; s}$.
$$@xrewrite2[split]{e[@SpillRegister{v_1; s}]; @Spill[get]{@SpillRegister{v_1; s}; v_2; e[@SpillRegister{v_2; s}]}}$$

In the third and final phase, when the register allocator determines that a variable should be
spilled, the $@SpillRegister{v; s}$ operands are selectively eliminated with the following rewrite.
$$@xrewrite[spill]{@SpillRegister{v; s}; @SpillMemory{s}}$$

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
