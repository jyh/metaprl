doc <:doc< -*- mode: text; -*-
   @begin[spelling]
   ML binop relop op AST compilable
   @end[spelling]

   @begin[doc]
   @subsubsection[m_doc_ir]{Intermediate representation}
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
@begin[doc]

The intermediate representation of the program must serve two
conflicting purposes.  It should be a fairly low-level language so
that translation to machine code is as straightforward as possible.
However, it should be abstract enough that program transformations and
optimizations need not be overly concerned with implementation detail.
The intermediate representation we use is similar to the functional
intermediate representations used by several groups
@cite["App92,fir-tr1,Tar97"], in which the language retains a similarity to an
ML-like language where intermediate values apart from arithmetic
expressions are explicitly named.

@begin[figure,ir]
$$
@begin[small]
@begin[array,cc]
@line{{@begin[array,rcll]
@line{@it{binop} {::=} {@AddOp @pipe @SubOp @pipe @MulOp @pipe @DivOp} @hbox{@it{Binary arithmetic}}}
@line{@it{relop} {::=} {@EqOp @pipe @NeqOp @pipe @cdots} @hbox{@it{Binary relations}}}
@line{{l}        {::=} {@it{string}} @hbox{@it{Function label}}}

@line{{}{}{}{}}
@line{{a} {::=}     {@AtomTrue @pipe @AtomFalse}          @hbox{@it{Boolean values}}}
@line{{}  {@pipe}   @AtomInt[i]                           @hbox{@it{Integers}}}
@line{{}  {@pipe}   @AtomVar{v}                           @hbox{@it{Variables}}}
@line{{}  {@pipe}   @AtomBinop{@it{binop}; a_1; a_2}      @hbox{@it{Binary arithmetic}}}
@line{{}  {@pipe}   @AtomRelop{@it{relop}; a_1; a_2}      @hbox{@it{Binary relations}}}
@line{{}  {@pipe}   @AtomFunVar{R; l}                     @hbox{@it{Function labels}}}
@end[array]} {@begin[array,rcll]
@line{{e} {::=}   @LetAtom{a; v; e}                        @hbox{@it{Variable definition}}}
@line{{}  {@pipe} @If{a; e_1; e_2}                         @hbox{@it{Conditional}}}
@line{{}  {@vdots} {} {}}
@line{{}  {@pipe} @Return{a}                               @hbox{@it{Return a value}}}
@line{{}  {@pipe} @TailCall{a; {a_1, @ldots, a_n}}         @hbox{@it{Tail-call}}}
@line{{}  {@pipe} @LetRec{R; d; e}                         @hbox{@it{Recursive functions}}}
@line{{}{}{}{}}
@line{{e_@lambda} {::=} {@AtomFun{v; e_@lambda} @pipe @AtomFun{v; e}} @hbox{@it{Functions}}}
@line{{d} {::=}   @FunDef{l; e_@lambda; d}                 @hbox{@it{Function definitions}}}
@line{{}  {@pipe} @EndDef                                  {}}
@end[array]}}
@end[array]
@end[small]
$$
@caption{Intermediate Representation}
@end[figure]

In this form, the IR is partitioned into two main parts: ``atoms''
define values like numbers, arithmetic, and variables; and
``expressions'' define all other computation.  The language includes
arithmetic, conditionals, tuples, functions, and function definitions.
A fragment of the language is shown in Figure @reffigure[ir].

@docoff
@end[doc]
>>

declare math_CloseVar{'v; 'e; 'a}
declare math_CloseRecVar{'R; 'frame}
declare math_CloseRec{'R; 'frame; 'tuple; 'fields; 'body}
declare math_CloseSubscript{'frame; 'index; 'v; 'e}
declare math_CloseFrame{'frame; 'e}

declare math_CloseVar{'v; 'a}
declare math_CloseRec{'R; 'frame; 'tuple}
declare math_CloseRecDefs{'d}
declare math_CloseRecBody{'e}

dform math_CloseVar_df1 : mode[tex] :: math_CloseVar{'v; 'e; 'a} =
   math_CloseVar{'v; 'a} slot{'e}

dform math_CloseVar_df2 : mode[tex] :: math_CloseVar{'v; 'a} =
   math_xlet slot{'v} `"=" slot{'a} math_xin

dform math_CloseRecVar_df : mode[tex] :: math_CloseRecVar{'R; 'frame} =
   slot{'R} `"(" slot{'frame} `")"

dform math_CloseRec_df_1 : mode[tex] :: math_CloseRec{'R; 'frame; 'tuple; 'd; 'e} =
   math_CloseRec{'R; 'frame; 'tuple}
   slot{'d} math_xin slot{'e}

dform math_CloseRec_df2 : mode[tex] :: math_CloseRec{'R; 'frame; 'tuple} =
   math_xlet math_xrec slot{'R} math_xwith `"[" slot{'frame} `"=" slot{'tuple} `"] ="

dform math_CloseRecDefs_df : mode[tex] :: math_CloseRecDefs{'d} =
   math_quad slot{'d}

dform math_CloseRecBody_df : mode[tex] :: math_CloseRecBody{'e} =
   math_xin slot{'e}

dform math_CloseSubscript_df : mode[tex] :: math_CloseSubscript{'a1; 'a2; 'v; 'e} =
    math_xlet slot{'v} `"= " slot{'a1} `".[" slot{'a2} `"]" math_xin slot{'e}

dform math_CloseFrame_df : mode[tex] :: math_CloseFrame{'frame; 'e} =
   math_bf["frame"] `"(" slot{'frame} `"," slot{'e} `")"

declare math_frame

dform math_frame_df : mode[tex] :: math_frame =
   math_it["Fr"]

doc <:doc<
@begin[doc]
@subsubsection[m_doc_closure]{Closure Conversion}

The program intermediate representation includes higher-order and nested functions.  The function
nesting must be eliminated before code generation, and the lexical scoping of function definitions
must be preserved when functions are passed as values.  This phase of program translation is
normally accomplished through @emph{closure conversion}, where the free variables for nested
functions are captured in an environment as passed to the function as an extra argument.  The
function body is modified so that references to variables that were defined outside the function are
now references to the environment parameter.  In addition, when a function is passed as a value, the
function is paired with the environment as a @emph{closure}.

The difficult part of closure conversion is the construction of the environment, and the
modification of variables in the function bodies.  We can formalize closure conversion as a sequence
of steps, each of which preserves the program's semantics.  In the first step, we must modify each
function definition by adding a new environment parameter.  To represent this, we replace each
$@LetRec{R; d; e}$ term in the program with a new term $@CloseRec{R; @frame; (); d; e}$,
where $@frame$ is an additional parameter, initialized to the empty tuple $()$, to be added to each
function definition.  Simultaneously, we replace every occurrence of the record variable $R$ with
$@CloseRecVar{R; @frame}$, which represents the partial application of the record $R$ to the tuple
$@frame$.

$$
@xrewrite2[frame]{@LetRec{R; d[R]; e[R]};
   @CloseRec{R; @frame; ();
            {d[@CloseRecVar{R; @frame}]};
            {e[@CloseRecVar{R; @frame}]}}}
$$

The second part of closure conversion does the closure operation using two operations.  For the first part,
suppose we have some expression $e$ with a free variable $v$.  We can abstract this variable using a
call-by-name function application as the expression $@CloseVar{v; e; v}$, which reduces to $e$ by
simple $@beta$-reduction.

$$@xrewrite[abs]{e[v]; @CloseVar{v; e[v]; v}}$$

By selectively applying this rule, we can quantify variables that occur free in the
function definitions $d$ in a term $@CloseRec{R; @frame; @it{tuple}; d; e}$.  The main closure
operation is the addition of the variable to the frame, using the following rewrite.

$$
@xrewrite2[close]{@begin[array,t,l]
                        @line{@CloseVar{v; a}}
                        @line{@CloseRec{R; @frame; {(a_1, @ldots, a_n)}}}
			@line{@CloseRecDefs{{d[R; v; @frame]}}}
			@line{@CloseRecBody{{e[R; v; @frame]}}}
                        @end[array];
   @begin[array,t,l]
   @line{@CloseRec{R; @frame; {(a_1, @ldots, a_n, a)}}}
   @line{@CloseRecDefs{@CloseSubscript{@frame; {n+1}; v; {d[R; v; @frame]}}}}
   @line{@CloseRecBody{@LetAtom{a; v; {e[R; v; @frame]}}}}
   @end[array]}
$$

Once all free variables have been added to the frame, the $@CloseRec{R; @frame; @it{tuple}; d; e}$
is rewritten to use explicit tuple allocation.

$$
@xrewrite2[alloc]{@begin[array,t,l]
	          @line{@CloseRec{R; @frame; @it{tuple}}}
	          @line{@CloseRecDefs{{d[R; @frame]}}}
                  @line{@CloseRecBody{{e[R; @frame]}}}
		  @end[array];
   @begin[array,t,l]
   @line{@LetRec{R; @CloseFrame{@frame; {d[R; @frame]}}}}
   @line{@LetTuple{@Length[n]; @it{tuple}; @frame; {e[R; @frame]}}}
   @end[array]}
$$

The final step of closure conversion is to propagate the subscript operations into the function bodies.

$$
@arraystretch{2}
@begin[array,l]

@line{@xrewrite2[arg]{@CloseFrame{@frame; @FunDef{l; @AtomFun{v; {e[@frame; v]}}; {d[@frame]}}};
   @FunDef{l; @AtomFun{@frame; @AtomFun{v; {e[@frame; v]}}}; @CloseFrame{@frame; {d[@frame]}}}}}

@line{@xrewrite2[sub]{@CloseSubscript{a_1; a_2; v_1; @FunDef{l; @AtomFun{v_2; {e[v_1; v_2]}}; {d[v_1]}}};
   @begin[array,t,l]
   @line{@FunDef{l; @AtomFun{v_2; @LetSubscript{a_1; a_2; v_1; {e[v_1; v_2]}}}}}
   @line{@CloseSubscript{a_1; a_2; v_1; {d[v_1]}}}
   @end[array]}}

@end[array]
$$

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
