(* -*- mode: text; -*- *)
doc <:doc<
   @spelling{max}

   @subsection[m_doc_x86_opt]{Assembly optimization}

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

doc <:doc<


There are several simple optimizations that can be performed on the generated assembly, including
dead-code elimination and reserve coalescing.  Dead-code elimination has a simple specification: any
instruction that defines a new binding variable can be eliminated if the variable is never used.
The following rewrites capture this property.
$$
@begin[array,l]
@line{@xrewrite[dmov]{@Mov{o; v; e}; e}}
@line{@xrewrite[dinst1]{@Inst1Reg[inst1]{o_r; v; e}; e}}
@line{@xrewrite[dinst2]{@Inst2Reg[inst2]{o; o_r; v; e}; e}}
@line{@xrewrite[dinst3]{@Inst3Reg[inst3]{o; o_{r_1}; o_{r_2}; v_1; v_2; e}; e}}
@end[array]
$$

As we mentioned in Section @refsection[m_doc_opt], this kind of dead-code elimination should not be
applied if the instruction being eliminated can raise an exception.

Another useful optimization is the coalescing of $@AsmReserve{i}$ instructions, which call the garbage
collector if $i$ bytes of storage are not available.  In the current version of the language, all
reservations specify a constant number of bytes of storage, and these reservations can be propagated
up the expression tree and coalesced.  The first step is an upward propagation of the reserve
statement.  The following rewrites illustrate the process.
$$
@begin[array,l]
@line{@xrewrite2[rmov]{@Mov{o; v; @AsmReserve{i; e[v]}}; @AsmReserve{i; @Mov{o; v; e[v]}}}}
@line{{}}
@line{@xrewrite2[rinst2]{@Inst2Reg[inst2]{o; o_r; v; @AsmReserve{i; e[v]}}; @AsmReserve{i; @Inst2Reg[inst2]{o; o_r; v; e[v]}}}}
@end[array]
$$

Adjacent reservations can also be coalesced.
$$@xrewrite2[rres]{@AsmReserve{i_1; @AsmReserve{i_2; e}}; @AsmReserve{i_1 + i_2; e}}$$

Two reservations at a conditional boundary can also be coalesced.  To ensure that both branches have
a reserve, it is always legal to introduce a reservation for $0$ bytes of storage.
$$
@begin[array,l]
@line{@xrewrite2[rif]{@Jcc[J]{@it[cc]; @AsmReserve{i_1; e_1}; @AsmReserve{i_2; e_2}}; @AsmReserve{{@it{max}(i_1; i_2)}; @Jcc[J]{@it[cc]; e_1; e_2}}}}
@line{{}}
@line{@xrewrite[rzero]{e; @AsmReserve{0; e}}}
@end[array]
$$

@docoff

>>

(*
 * -*-
 * Local Variables:
 * fill-column: 100
 * End:
 * -*-
 *)
