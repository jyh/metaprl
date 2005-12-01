(* -*- mode: text; -*- *)
doc <:doc<
   @begin[spelling]
   ML binop relop op AST compilable marks
   @end[spelling]

   @section[m_doc_ir]{Intermediate representation}
   @docoff
   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2003-2005 Mojave Group, Caltech

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}
   Modified by: Mojave Group
   @end[license]
>>
extends M_doc_comment

(*
 * IR conversion term.
 *)
declare math_IR{'e}
declare math_IR{'e1; 'v}
declare math_IR{'e1; 'v; 'e2['v]}

dform math_IR_df1 : mode[tex] :: math_IR{'e1} =
   math_semleft slot{'e1} math_subscript{math_semright; math_it["IR"]}

dform math_IR_df2 : mode[tex] :: math_IR{'e1; 'v} =
   math_semleft slot{'e1} math_subscript{math_semright; math_it["IR"]} slot{'v} `"."

dform math_IR_df3 : mode[tex] :: math_IR{'e1; 'v; 'e2} =
   math_semleft slot{'e1} math_subscript{math_semright; math_it["IR"]} slot{'v} `"." slot{'e2}

(*
 * Params come from the parser.
 *)
declare math_AtomParam{'v; 'e}

dform math_AtomParam_df : mode[tex] :: math_AtomParam{'x; 'e} =
   math_subscript{lambda; math_it["p"]} slot{'x} `"." slot{'e}

(*
 * Math mode versions.
 *)
declare math_AddOp
declare math_SubOp
declare math_MulOp
declare math_DivOp

declare math_LtOp
declare math_LeOp
declare math_EqOp
declare math_NeqOp
declare math_GeOp
declare math_GtOp

dform math_AddOp_df1 : math_AddOp =
   `"+"

dform math_SubOp_df1 : math_SubOp =
   `"-"

dform math_MulOp_df1 : math_MulOp =
   `"*"

dform math_DivOp_df1 : math_DivOp =
   `"/"

dform math_LtOp_df1 : math_LtOp =
   `"<"

dform math_LeOp_df1 : mode[tex] :: math_LeOp =
   izone `"\\le " ezone

dform math_LeOp_df2 : except_mode[tex] :: math_LeOp =
   `"<="

dform math_EqOp_df1 : math_EqOp =
   `"="

dform math_NeqOp_df1 : math_NeqOp =
   `"<>"

dform math_GeOp_df1 : mode[tex] :: math_GeOp =
   izone `"\\ge " ezone

dform math_GeOp_df2 : except_mode[tex] :: math_GeOp =
   `">="

dform math_GtOp_df1 : math_GtOp =
   `">"

declare math_AtomFalse
declare math_AtomTrue
declare math_AtomInt[i:s]
declare math_AtomBinop{'op; 'a1; 'a2}
declare math_AtomRelop{'op; 'a1; 'a2}
declare math_AtomFun{'x; 'e}
declare math_AtomVar{'v}
declare math_AtomFunVar{'R; 'v}

dform math_AtomFalse_df : mode[tex] :: math_AtomFalse =
   izone `"\\bot " ezone

dform math_AtomTrue_df : mode[tex] :: math_AtomTrue =
   izone `"\\top " ezone

dform math_AtomInt_df : mode[tex] :: math_AtomInt[i:s] =
   slot[i:s]

dform math_AtomBinop_df : mode[tex] :: math_AtomBinop{'op; 'a1; 'a2} =
   slot{'a1} math_mathrel{slot{'op}} slot{'a2}

dform math_AtomRelop_df : mode[tex] :: math_AtomRelop{'op; 'a1; 'a2} =
   slot{'a1} math_mathrel{slot{'op}} slot{'a2}

dform math_AtomFun_df : mode[tex] :: math_AtomFun{'x; 'e} =
   lambda slot{'x} `"." slot{'e}

dform math_AtomVar_Df : mode[tex] :: math_AtomVar{'v} =
   slot{'v}

dform math_AtomFunVar_df : mode[tex] :: math_AtomFunVar{'R; 'v} =
   slot{'R} `"." slot{'v}

(*
 * Expressions.
 *)
declare math_LetAtom{'a; 'v; 'e['v]}
declare math_If{'a; 'e1; 'e2}

declare math_ArgNil
declare math_ArgCons{'a; 'rest}
declare math_TailCall{'f; 'args}

declare math_Length[i:s]
declare math_AllocTupleNil
declare math_AllocTupleCons{'a; 'rest}
declare math_LetTuple{'length; 'tuple; 'v; 'e['v]}
declare math_LetSubscript{'a1; 'a2; 'v; 'e['v]}
declare math_SetSubscript{'a1; 'a2; 'a3; 'e}

declare math_LetApply{'f; 'a; 'v; 'e['v]}
declare math_LetClosure{'a1; 'a2; 'f; 'e['f]}
declare math_Return{'a}

declare math_SetSubscript{'a1; 'a2; 'a3}

dform math_LetAtom_df : mode[tex] :: math_LetAtom{'a; 'v; 'e} =
   math_xlet slot{'v} `"=" slot{'a} math_xin slot{'e}

dform math_If_df : mode[tex] :: math_If{'a; 'e1; 'e2} =
   math_xif slot{'a} math_xthen slot{'e1} math_xelse slot{'e2}

dform math_TailCall_df : mode[tex] :: math_TailCall{'f; 'args} =
   slot{'f} `"(" slot{'args} `")"

dform math_LetTuple_df : mode[tex] :: math_LetTuple{'length; 'tuple; 'v; 'e} =
   math_xlet slot{'v} `"= (" slot{'tuple} `")" math_xin slot{'e}

dform math_LetSubscript_df : mode[tex] :: math_LetSubscript{'a1; 'a2; 'v; 'e} =
   math_xlet slot{'v} `"= " slot{'a1} `".[" slot{'a2} `"]" math_xin slot{'e}

dform math_SetSubscript_df1 : mode[tex] :: math_SetSubscript{'a1; 'a2; 'a3} =
   slot{'a1} `".[" slot{'a2} `"]" leftarrow slot{'a3} `";"

dform math_SetSubscript_df2 : mode[tex] :: math_SetSubscript{'a1; 'a2; 'a3; 'e} =
   slot{'a1} `".[" slot{'a2} `"]" leftarrow slot{'a3} `";" slot{'e}

dform math_LetApply_df : mode[tex] :: math_LetApply{'f; 'a; 'v; 'e} =
   math_xlet slot{'v} `"=" slot{'f} `"(" slot{'a} `")" math_xin slot{'e}

dform math_LetClosure_df : mode[tex] :: math_LetClosure{'f; 'a; 'v; 'e} =
   math_mathop{math_bf["letc"]} slot{'v} `"=" slot{'f} `"(" slot{'a} `")" math_xin slot{'e}

dform math_Return_df : mode[tex] :: math_Return{'a} =
   math_bf["return "] slot{'a}

(*
 * Recursive functions.
 *)
declare math_LetRec{'R; 'e1; 'e2}
declare math_LetRec{'R; 'e1}
declare math_LetRec{'R}
declare math_LetRecDef{'d}
declare math_LetRecBody{'e}

declare math_Fields{'fields}
declare math_Label[tag:s]

declare math_FunDef{'label; 'exp; 'rest}
declare math_FunDef{'label; 'exp}

declare math_EndDef
declare math_LetFun{'R; 'label; 'f; 'e}

(* Ignore the second record *)
dform math_LetRec_df1 : mode[tex] :: math_LetRec{'R} =
   math_xlet math_bf[" rec "] slot{'R} `"="

dform math_LetRecDef_df : mode[tex] :: math_LetRecDef{'d} =
   math_quad slot{'d}

dform math_LetRecBody_df : mode[tex] :: math_LetRecBody{'e} =
   math_xin slot{'e}

dform math_LetRec_df2 : mode[tex] :: math_LetRec{'R; 'e1} =
   math_xlet math_bf[" rec "] slot{'R} `"=" slot{'e1} math_xin

dform math_LetRec_df3 : mode[tex] :: math_LetRec{'R; 'e1; 'e2} =
   math_xlet math_bf[" rec "] slot{'R} `"=" slot{'e1} math_xin slot{'e2}

dform math_Fields_df : mode[tex] :: math_Fields{'fields} =
   slot{'fields}

dform math_FunDef_df1 : mode[tex] :: math_FunDef{'label; 'exp} =
   math_bf["fun "] slot{'label} `"=" slot{'exp} math_xand

dform math_FunDef_df2 : mode[tex] :: math_FunDef{'label; 'exp; 'rest} =
   math_bf["fun "] slot{'label} `"=" slot{'exp} math_xand slot{'rest}

dform math_EndDef_df : mode[tex] :: math_EndDef =
   epsilon

doc <:doc<

The intermediate representation of the program must serve two
conflicting purposes.  It should be a fairly low-level language so
that translation to machine code is as straightforward as possible.
However, it should be abstract enough that program transformations and
optimizations need not be overly concerned with implementation detail.
The intermediate representations we use throughout this work are variants of A-normal form
@cite[FSDF93].  These representations are similar to the functional
intermediate representations used by several groups
@cite["App92,fir-tr1,Tar97"], in which the language retains a similarity to an
ML-like language where all intermediate values apart from arithmetic
expressions are explicitly named.

@begin[figure,ir]
$$
@begin[array,"r@{}c@{}ll"]
@line{@it{binop} {@space ::= @space} {@AddOp @vbar @SubOp @vbar @MulOp @vbar @DivOp} @hbox{Binary arithmetic}}
@line{@it{relop} {::=} {@EqOp @pipe @NeqOp @pipe @LeOp @pipe @LtOp @pipe @GeOp @pipe @GtOp} @hbox{Binary relations}}
@line{{l}        {::=} {@it{string}} @hbox{Function label}}

@line{{}{}{}{}}
@line{{a} {::=}     {@AtomTrue @pipe @AtomFalse}          @hbox{Boolean values}}
@line{{}  {@pipe}   @AtomInt[i]                           @hbox{Integers}}
@line{{}  {@pipe}   @AtomVar{v}                           @hbox{Variables}}
@line{{}  {@pipe}   @AtomBinop{@it{binop}; a_1; a_2}      @hbox{Binary arithmetic}}
@line{{}  {@pipe}   @AtomRelop{@it{relop}; a_1; a_2}      @hbox{Binary relations}}
@line{{}  {@pipe}   @AtomFunVar{R; l}                     @hbox{Function labels}}

@line{{}{}{}{}}
@line{{e} {::=}   @LetAtom{a; v; e}                        @hbox{Variable definition}}
@line{{}  {@pipe} @If{a; e_1; e_2}                         @hbox{Conditional}}
@line{{}  {@pipe} @LetTuple{i; {a_1, @ldots, a_n}; v; e}   @hbox{Tuple allocation}}
@line{{}  {@pipe} @LetSubscript{a_1; a_2; v; e}            @hbox{Subscripting}}
@line{{}  {@pipe} @SetSubscript{a_1; a_2; a_3; e}          @hbox{Assignment}}
@line{{}  {@pipe} @LetApply{a; {a_1, @ldots, a_n}; v; e}   @hbox{Function application}}
@line{{}  {@pipe} @LetClosure{a_1; a_2; v; e}              @hbox{Closure creation}}
@line{{}  {@pipe} @Return{a}                               @hbox{Return a value}}
@line{{}  {@pipe} @TailCall{a; {a_1, @ldots, a_n}}         @hbox{Tail-call}}
@line{{}  {@pipe} @LetRec{R; d; e}                         @hbox{Recursive functions}}
@line{{}{}{}{}}
@line{{e_@lambda} {::=} {@AtomFun{v; e_@lambda} @vbar @AtomFun{v; e}} @hbox{Functions}}
@line{{d} {::=}   @FunDef{l; e_@lambda; d}                 @hbox{Function definitions}}
@line{{}  {@pipe} @EndDef                                  {}}
@end[array]
$$
@caption{Intermediate Representation}
@end[figure]

In this form, the IR is partitioned into two main parts: ``atoms''
define values like numbers, arithmetic, and variables; and
``expressions'' define all other computation.  The language includes
arithmetic, conditionals, tuples, functions, and function definitions,
as shown in Figure @reffigure[ir].

Function definitions deserve special mention.  Functions are defined using the $@LetRec{R; d; e}$
term, where $d$ is a list of mutually recursive functions, and variable $R$
represents a recursively defined
record containing these functions.  Each of the functions is labeled, and the term $@AtomFunVar{R;
l}$ represents the function with label $l$ in record $R$.

While this representation has an easy formal interpretation as a fixpoint of the single variable
$R$, it is awkward to use, principally because it violates the rule of higher-order abstract syntax:
namely, that (function) variables be represented as variables in the meta-language.  We are
currently investigating the use of @emph{sequents} to represent mutual recursion in order to address
these problems.

@subsection[m_ir_conv]{AST to IR conversion}

The main difference between the abstract syntax representation and the
IR is that intermediate expressions in the AST do not have to be
named.  In addition, the conditional in the AST can be used anywhere
an expression can be used (for instance, as the argument to a
function), while in the IR, the branches of the conditional must be
terminated by a $@Return{a}$ expression or tail-call.

The translation from AST to IR is straightforward, but we use it to
illustrate a style of translation we use frequently.  We introduce an administrative term
$@tt{IR} @lbrace e_1; v. e_2[v] @rbrace$ (displayed as $@IR{e_1; v;
e_2[v]}$) that represents the translation of an expression $e_1$ to an IR atom. The second argument ($e_2[v]$)
is a @emph{meta-continuation} of the translation process. In other words, $e_2$ represents @emph{the
rest} of the program and $v$ marks the location where the IR for $e_1$ would go.

The translation
problem is expressed through the following rule, which states that a
program $e$ is compilable if the program can be translated to an atom,
returning the value as the result of the program.
$$
@begin[array,c]
@line{{@Gamma @vdash @compilable{@IR{e; v; @Return{v}}}}}
@hline
@line{{@Gamma @vdash @compilable{e}}}
@end[array]
$$

For many AST expressions, the translation to IR is straightforward.  The following rules give a few
representative examples.  Note that all the rules perform substitution, which is
specified implicitly using higher-order abstract syntax.
$$
@begin[array,l]
@line{@xrewrite[int]{@IR{i; v; e[v]}; e[@AtomInt[i]]}}
@line{{}}
@line{@xrewrite[var]{@IR{v_1; v_2; e[v_2]}; e[@AtomVar{v_1}]}}
@line{{}}
@line{@xrewrite2[add]{@IR{{e_1 + e_2}; v; e[v]};
		        @IR{e_1; v_1; @IR{e_2; v_2; e[@AtomBinop{+; v_1; v_2}]}}}}
@line{{}}
@line{@xrewrite2[set]{@IR{e_1.[e_2] @leftarrow e_3; v; e_4[v]};
    @begin[array,t,l]
    @line{@IR{e_1; v_1}}
    @line{@IR{e_2; v_2}}
    @line{@IR{e_3; v_3}}
    @line{@SetSubscript{v_1; v_2; v_3}}
    @line{{e_4[@AtomFalse]}}
    @end[array]}}
@end[array]
$$
Here @xrewref[int] and @xrewref[var] specify that variables and numerical constants do not have to
be further translated --- so we simply pass the original variable or numerical constant to
meta-continuation. The @xrewref[add] rewrite specifies that in order to translate $e_1 + e_2$, we
need to first translate $e_1$ (passing the result as $v_1$), continuing with translation of $e_2$
(passing the result as $v_2$), continuing with passing the IR expression $@AtomBinop{+; v_1; v_2}$ to
the original meta-continuation.

For conditionals, code duplication is avoided by wrapping the code
after the conditional in a function, and calling the function at the
tail of each branch of the conditional.
$$
@xrewrite2[if]{@IR{@If{e_1; e_2; e_3}; v; e_4[v]};
    @begin[array,t,l]
    @line{@LetRec{R; @FunDef{g; @AtomFun{v; e_4[v]}; @EndDef}}}
    @line{@IR{e_1; v_1}}
    @line{@If{v_1; @IR{e_2; v_2; (@TailCall{@AtomFunVar{R; g}; v_2})}; @IR{e_3; v_3; (@TailCall{@AtomFunVar{R; g}; v_3})}}}
    @end[array]}
$$

For functions, the post-processing phase converts recursive function
definitions to the record form, and we have the following translation,
using the term $@IR{d}$ to translate function definitions.  In
general, anonymous functions must be named @emph{except} when they are
outermost in a function definition.  The post-processing phase
produces two kinds of $@lambda$-abstractions, the $@AtomParam{v;
e[v]}$ is used to label function parameters in recursive definitions,
and the $@AtomFun{v; e[v]}$ term is used for anonymous functions.
$$
@begin[array,l]
@line{@xrewrite2[letrec]{@IR{@LetRec{R; d; e_1}; v; e_2[v]};
    @LetRec{R; @IR{d}; @IR{e_1; v; e_2[v]}}}}
@line{{}}
@line{@xrewrite2[fun]{@IR{@FunDef{l; e; d}}; @FunDef{l; @IR{e; v; @Return{v}}; @IR{d}}}}
@end[array]
$$
$$
@begin[array,l]
@line{@xrewrite2[param]{@IR{@AtomParam{v_1; e_1[v_1]}; v_2; e_2[v_2]};
   @AtomFun{v_1; (@IR{e_1[v_1]; v_2; e_2[v_2]})}}}
@line{{}}
@line{@xrewrite2[abs]{@IR{@AtomFun{v_1; e_1[v_1]}; v_2; e_2[v_2]};
   @begin[array,t,l]
   @line{@LetRec{R}}
   @line{@LetRecDef{@FunDef{g; @AtomFun{v_1; @IR{e_1[v_1]; v_3; @Return{v_3}}}; @EndDef}}}
   @line{@LetRecBody{{e_2[@AtomFunVar{R; g}]}}}
   @end[array]}}
@end[array]
$$

All the rewrites for the AST to IR translation are automatically collected by the @MetaPRL system
into a syntax-directed lookup table (each rewrite is annotated with the name of the appropriate table)
and creates the tactic for sweeping the program and performing all the applicable transformations
@cite[HN04].

>>

(*
 * -*-
 * Local Variables:
 * fill-column: 100
 * End:
 * -*-
 *)
