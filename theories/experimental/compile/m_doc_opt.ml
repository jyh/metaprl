doc <:doc< -*- mode: text; -*-
   @begin[spelling]
   IR inlined binop relop op
   @end[spelling]
  
   @begin[doc]
   @subsection[m_doc_opt]{IR optimizations}
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

doc <:doc< 
@begin[doc]

Many optimizations on the intermediate representation are quite easy to express.  For illustration,
we include two very simple optimizations: dead-code elimination and constant folding.

@subsubsection["dce"]{Dead code elimination}

Formally, an expression $e$ in a program $p$ is dead if the removal of expression $e$ does not
change the behavior of the program $p$.  Complete elimination of dead-code is undecidable: for
example, an expression $e$ is dead if no program execution ever reaches expression $e$.  The most
frequent approximation is based on scoping: a let-expression $@LetAtom{a; v; e}$ is dead if $v$ is
not free in $e$.  This kind of dead-code elimination can be specified with the following
set of rewrites.
$$
@begin[array,l]
@line{@xrewrite[datom]{@LetAtom{a; v; e}; e}}
@line{@xrewrite[dtuple]{@LetTuple{@Length[i]; {a_1, @ldots, a_n}; v; e}; e}}
@line{@xrewrite[dsub]{@LetSubscript{a_1; a_2; v; e}; e}}
@line{@xrewrite[dcl]{@LetClosure{a_1; a_2; v; e}; e}}
@end[array]
$$

The syntax of these rewrites depends on the second-order specification of substitution.  Note that
the pattern $e$ is @emph{not} expressed as the second-order pattern $e[v]$.  That is, $v$ is
@emph{not} allowed to occur free in $e$.

Furthermore, note that dead-code elimination of this form is aggressive.  For example, suppose we
have an expression $@LetAtom{@AtomBinop{/; a; @AtomInt[0]}; v; e}$.  This expression is considered
as dead-code even though division by $0$ is not a valid operation.  If the target architecture
raises an exception on division by zero, this kind of aggressive dead-code elimination is unsound.
This problem can be addressed formally by partitioning the class of atoms into two parts: those that
may raise an exception, and those that do not, and applying dead-code elimination only on the first
class.  The rules for dead-code elimination are the same as above, where the calls of atom $a$
refers only to those atoms that do not raise exceptions.

@subsubsection["constant-folding"]{Constant-folding}

Another simple class of optimizations is constant folding.  If we have an expression that includes
only constant values, the expression may be computed at compile time.  The following rewrite
captures the arithmetic part of this optimization, where $@semleft @it{op} @semright$ is the
interpretation of the arithmetic operator in the meta-language.  Relations and conditionals can be
folded in a similar fashion.
$$
@begin[array,l]
@line{@xrewrite[binop]{@AtomBinop{@it{binop}; @AtomInt[i]; @AtomInt[j]}; {@semleft @it{op} @semright(i, j)}}}
@line{@xrewrite[relop]{@AtomRelop{@it{relop}; @AtomInt[i]; @AtomInt[j]}; {@semleft @it{op} @semright(i, j)}}}
@line{@xrewrite[ift]{@If{@AtomTrue; e_1; e_2}; e_1}}
@line{@xrewrite[iff]{@If{@AtomFalse; e_1; e_2}; e_2}}
@end[array]
$$

In order for these transformations to be faithful, the arithmetic must be performed over the numeric
set provided by the target architecture (our implementation, described in Section
@refsection[m_doc_x86_codegen], uses 31-bit signed integers).

For simple constants $a$, it is usually more efficient to inline the $@LetAtom{a; v; e[v]}$ expression as well.
$$
@begin[array,l]
@line{@xrewrite[cint]{@LetAtom{@AtomInt[i]; v; e[v]}; e[@AtomInt[i]]}}
@line{@xrewrite[cfalse]{@LetAtom{@AtomFalse; v; e[v]}; e[@AtomFalse]}}
@line{@xrewrite[ctrue]{@LetAtom{@AtomTrue; v; e[v]}; e[@AtomTrue]}}
@line{@xrewrite[cvar]{@LetAtom{@AtomVar{v_1}; v_2; e[v_2]}; e[v_1]}}
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
