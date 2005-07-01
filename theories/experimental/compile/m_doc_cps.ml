(* -*- mode: text; -*- *)
doc <:doc<
   @begin[spelling]
   CPS compilable exp
   @end[spelling]

   @subsection[m_doc_cps]{CPS conversion}

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
extends M_doc_ir

declare math_CPSRecordVar{'R}
declare math_CPSFunVar{'f}

declare math_cont
declare math_CPS{'a}
declare math_CPS{'cont; 'e}

dform math_CPSRecordVar_df : mode[tex] :: math_CPSRecordVar{'R} =
   slot{'R} math_bf["[id]"]

dform math_CPSFunVar_df : mode[tex] :: math_CPSFunVar{'f} =
   slot{'f} math_bf["[id]"]

dform math_cont_df : mode[tex] :: math_cont =
   `"c"

dform math_CPS_df : mode[tex] :: math_CPS{'a} =
   math_bf["CPS("] slot{'a} math_bf[")"]

dform math_CPS_df2 : mode[tex] :: math_CPS{'cont; 'e} =
   math_semleft slot{'e} math_subscript{math_semright; math_cont}

doc <:doc<

CPS conversion is an optional phase of the compiler that converts the program to
continuation-passing style.  That is, instead of returning a value, functions pass their results to
a continuation function that is passed as an argument.  In this phase, all functions become
tail-calls, and all occurrences of $@LetApply{a_1; a_2; v; e}$ and $@Return{a}$ are eliminated.  The
main objective in CPS conversion is to pass the result of the computation to a continuation
function.

There are different ways of formalizing the CPS conversion (see Section @refsection[m_doc_summary]
for a discussion). In this compiler we used the following inference rule, which states that a program $e$
is compilable if for all functions $@cont$, the program $@CPS{@cont; e}$ is compilable.
$$@mbox{@misspelled{[cps_prog]}}~~~
@begin[array,c]
@line{{@Gamma, @cont @colon @it{exp} @vdash @compilable{@CPS{@cont; e}}}}
@hline
@line{{@Gamma @vdash @compilable{e}}}
@end[array]
$$

The term $@CPS{@cont; e}$ represents the application of the $@cont$ function to the program
$e$, and we can use it to transform the program $e$ by migrating the call to the continuation
downward in the expression tree.  Abstractly, the process proceeds as follows.

@begin[itemize]

@item{{First, replace each function definition $f = @AtomFun{x; e[x]}$ with a continuation form $f =
@AtomFun{@cont; @AtomFun{x; @CPS{@cont; e[x]}}}$ and simultaneously replace all occurrences of $f$
with the partial application $@CPSFunVar{f}$, where $@bf[id]$ is the identity function.}}

@item{{Next, replace tail-calls $@CPS{@cont; @TailCall{@CPSFunVar{f}; {a_1, @ldots, a_n}}}$ with
$@TailCall{@AtomVar{f}; {@cont, a_1, @ldots, a_n}}$, and return statements $@CPS{@cont; @Return{a}}$
with $@TailCall{@cont; a}$.}}

@item{{Finally, replace inline-calls $@CPS{@cont; @LetApply{@CPSFunVar{f}; {a_1, @ldots, a_n}; v;
e}}$ with the continuation-passing version $@LetRec{R; @FunDef{g; @AtomFun{v; @CPS{@cont; e}};
@EndDef}; @TailCall{f; {g, a_1, @ldots, a_n}}}$.}}

@end[itemize]

For many expressions, CPS conversion is a straightforward mapping of the CPS translation, as shown
by the following five rules.
$$
@arraystretch{2}
@begin[array,l]
@line{@xrewrite[atom]{@CPS{@cont; @LetAtom{a; v; e[v]}}; @LetAtom{a; v; @CPS{@cont; e[v]}}}}
@line{@xrewrite2[tuple]{@CPS{@cont; @LetTuple{i; {a_1, @ldots, a_n}; v; e[v]}}; @LetTuple{i; {a_1, @ldots, a_n}; v; @CPS{@cont; e[v]}}}}
@line{@xrewrite2[letsub]{@CPS{@cont; @LetSubscript{a_1; a_2; v; e[v]}}; @LetSubscript{a_1; a_2; v; @CPS{@cont; e[v]}}}}
@line{@xrewrite[setsub]{@CPS{@cont; @SetSubscript{a_1; a_2; a_3; e[v]}}; @SetSubscript{a_1; a_2; a_3; @CPS{@cont; e[v]}}}}
@line{@xrewrite2[if]{@CPS{@cont; @If{a; e_1; e_2}}; @If{a; @CPS{@cont; e_1}; @CPS{@cont; e_2}}}}
@end[array]
$$

The modification of functions is the key part of the conversion.  When a $@LetRec{R; d[R]; e[R]}$
term is converted, the goal is to add an extra continuation parameter to each of the functions in
the recursive definition.  Conversion of the function definition is shown in the
@misspelled{@em{fundef}} rule, where the function gets an extra continuation argument that is then
applied to the function body.

In order to preserve the program semantics, we must then replace all occurrences of the function with
the term $@CPSFunVar{f}$, which represents the partial application of the function to the identity.
This step is performed in two parts: first the @misspelled{@em{letrec}} rule replaces all
occurrences of the record variable $R$ with the term $@CPSRecordVar{R}$, and then the
@misspelled{@em{letfun}} rule replaces each function variable $f$ with the term $@CPSFunVar{f}$.
$$
@arraystretch{2}
@begin[array,l]
@line{@xrewrite2[letrec]{@CPS{@cont; @LetRec{R; d[R]; e[R]}};
      @LetRec{R; @CPS{@cont; d[@CPSRecordVar{R}]}; @CPS{@cont; e[@CPSRecordVar{R}]}}}}
@line{@xrewrite2[fundef]{@CPS{@cont; @FunDef{l; @AtomFun{v; e[v]}; d}};
                @FunDef{l; @AtomFun{@cont; @AtomFun{v; @CPS{@cont; e[v]}}}; @CPS{@cont; d}}}}
@line{@xrewrite[enddef]{@CPS{@cont; @EndDef}; @EndDef}}
@line{@xrewrite2[letfun]{@CPS{@cont; @LetAtom{@AtomFunVar{@CPSRecordVar{R}; l}; v; e[v]}};
                        @LetAtom{@AtomFunVar{R; l}; v; @CPS{@cont; e[@CPSFunVar{v}]}}}}
@end[array]
$$

Non-tail-call function applications must also be converted to continuation passing form, as shown in
the @em{apply} rule, where the expression @em{after} the function call is wrapped in a continuation
function and passed as a continuation argument.
$$
@begin[array,l]
@line{@xrewrite2[apply]{@CPS{@cont; @LetApply{@CPSFunVar{v_1}; a; v_2; e[v_2]}};
      @begin[array,t,l]
      @line{@LetRec{R; @FunDef{g; @AtomFun{v; @CPS{@cont; e[v]}}; @EndDef}}}
      @line{@LetAtom{@AtomFunVar{R; g}; g; @TailCall{@AtomVar{f}; {@AtomVar{g}; @AtomVar{a}}}}}
      @end[array]}}
@end[array]
$$

In the final phase of CPS conversion, we can replace return statements with a call to the
continuation.  For tail-calls, we replace the partial application of the function $@CPSFunVar{f}$
with an application to the continuation.
$$
@begin[array,l]
@line{@xrewrite[return]{@CPS{@cont; @Return{a}}; @TailCall{@cont; a}}}
@line{@xrewrite[tailcall]{@CPS{@cont; @TailCall{@CPSFunVar{f}; {a_1, @ldots, a_n}}};
                @TailCall{@AtomVar{f}; {@cont, a_1, @ldots, a_n}}}}
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
