doc <:doc< -*- mode: text; -*-
   @begin[spelling]
   CPS
   @end[spelling]
  
   @begin[doc]
   @subsection[m_doc_closure]{Closure conversion}
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

declare math_CloseVar{'v; 'e; 'a}
declare math_CloseRecVar{'R; 'frame}
declare math_CloseRec{'R; 'frame; 'tuple; 'fields; 'body}
declare math_CloseSubscript{'frame; 'index; 'v; 'e}
declare math_CloseFrame{'frame; 'e}

declare math_CloseVar{'v; 'a}
declare math_CloseRec{'R; 'frame; 'tuple}
declare math_CloseRecDefs{'d}
declare math_CloseRecBody{'e}
declare math_CloseSubscript{'frame; 'index; 'v}

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
   
dform math_CloseSubscript_df : mode[tex] :: math_CloseSubscript{'a1; 'a2; 'v} =
    math_xlet slot{'v} `"= " slot{'a1} `".[" slot{'a2} `"]" math_xin

dform math_CloseSubscript_df : mode[tex] :: math_CloseSubscript{'a1; 'a2; 'v; 'e} =
    math_CloseSubscript{'a1; 'a2; 'v} slot{'e}

dform math_CloseFrame_df : mode[tex] :: math_CloseFrame{'frame; 'e} =
   math_bf["frame"] `"(" slot{'frame} `"," slot{'e} `")"

declare math_frame

dform math_frame_df : mode[tex] :: math_frame =
   math_it["Fr"]
   
doc <:doc< 
@begin[doc]

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
operation is the addition of the abstracted variable to the frame, using the following rewrite.
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

@line{@xrewrite2[sub]{
   @begin[array,t,l]
   @line{@CloseSubscript{a_1; a_2; v_1}}
   @line{@FunDef{l; @AtomFun{v_2; {e[v_1; v_2]}}; {d[v_1]}}}
   @end[array];
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
