doc <:doc< -*- mode: text; -*-
   @begin[spelling]
   CPS grunge Liang Morrisett Necula untrusted
   @end[spelling]
  
   @begin[doc]
   @section[m_doc_summary]{Summary and Future Work}
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

doc <:doc< 
@begin[doc]

One of the points we have stressed in this presentation is that the formalized versions of these
algorithms is easy, in fact easier than the definition using traditional general-purpose languages.
By adding these algorithms to the FDL, the formal description is freely-available for use in a wide
variety of applications.  This will increase the reliability of these algorithms, because the
algorithm description is @emph{verifiable}, and it will make development easier, by providing a
common implementation.

The formal development of these algoriths was eased for several reasons.  @MetaPRL provided a great
deal of automation for frequently occurring tasks.  In most cases, the implementation of a new
compiler phase meant only the development of new rewrite rules.  There is very little of the
``grunge'' code that plagues traditional implementations, such as the maintenance of tables that
keep track of the variables in scope, code-walking procedures to apply a transformation to the
program's subterms, and other kinds of housekeeping code.

As a basis of comparison, we can compare the formal compiler in this paper to a similar native-code
compiler for a fragment of the Java language we developed as part of the Mojave project
@cite[MojaveHome].  The Java compiler is written in @OCaml, and uses an intermediate representation
similar to the one presented in this paper, with two main differences: the Java intermediate
representation is typed, and the x86 assembly language is not scoped.

Figure @reffigure[locxxx] gives a comparison of some of the key parts of both compilers in terms of
lines of code, where we omit code that implements the Java type system and class constructs.  The
formal compiler columns list the total lines of code for the term rewrites, as well as the total
code including rewrite strategies.  The size of the total code base in the formal compiler is still
quite large due to the extensive code needed to implemented the graph coloring algorithm for the
register allocator.  Preliminary tests suggest that performance of programs generated from the formal compiler is comparable,
sometimes better than, the Java compiler due to a better spilling strategy.

@begin[figure,locxxx]
@begin[center]
@begin[tabular,"|llll|"]
@hline
@line{{Description}        @multicolumn[2,l]{Formal compiler} {Java}}
@line{{}                   {Rewrites} {Total}            {}}
@hline
@line{{CPS conversion}     {44}       {347}                   {338}}
@line{{Closure conversion} {54}       {410}                   {1076}}
@line{{Code generation}    {214}      {648}                   {1012}}
@line{{Total code base}    {484}      {10000}                 {12000}}
@hline
@end[tabular]
@end[center]
@caption{Code comparison}
@end[figure]

The work presented in this paper took roughly one person-week of effort from concept to
implementation, while the Java implementation took roughly three times as long.  It should be noted
that, while the Java compiler has been stable for about a year, it still undergoes periodic
debugging.  Register allocation is especially problematic to debug in the Java compiler, since
errors are not caught at compile time, but typically cause memory faults in the generated program.

This work is far from complete.  The current example serves as a proof of concept, but it remains to
be seen what issues will arise when the formal compilation methodology is applied to more complex
programming languages.  For future work, we intend to approach the problem of developing and
validating formal compilers in three steps.  The first step is the development of typed intermediate
languages.  These languages admit a broader class of rewrite transformations that are conditioned on
well-typed programs, and the typed language serves as a launching point for compiler validation.
The second step is to develop a semantics of the intermediate language and validate the rewrite
rules for a small source language similar to the one presented here.  It is not clear whether the
same properties should be applied to the assembly language---whether the assembly language should be
typed, and whether it is feasible to develop a simple formal model of the target architecture that
will allow the code generation and register allocations phases to be verified.  The final step is to
extend the source language to one resembling a modern general-purpose language.

@section["related-work"]{Related work}

@comment{The use of higher-order abstract syntax, logical environments, and
term rewriting for compiler implementation and validation are not new
areas individually.}

Term rewriting has been successfully used to describe programming
language syntax and semantics, and there are systems that provide
efficient term representations of programs as well as rewrite rules
for expressing program transformations. For instance, the
@tt["ASF+SDF"] environment @cite[BHKO02] allows the programmer to
construct the term representation of a wide variety of programming
syntax and to specify equations as rewrite rules.  These rewrites may
be conditional or unconditional, and are applied until a normal form
is reached.  Using equations, programmers can specify optimizations,
program transformations, and evaluation.  The @tt["ASF+SDF"] system
targets the generation of informal rewriting code that can be used in
a compiler implementation.

Liang @cite[Lia02] implemented a compiler for a simple imperative
language using a higher-order abstract syntax implementation in
$@lambda$Prolog.  Liang's approach includes several of the phases we
describe here, including parsing, CPS conversion, and code generation
using a instruction set defined using higher-abstract syntax (although
in Liang's case, registers are referred to indirectly through a
meta-level store, and we represent registers directly as variables).
Liang does not address the issue of validation in this work, and the
primary role of $@lambda$Prolog is to simplify the compiler
implementation.  In contrast to our approach, in Liang's work the
entire compiler was implemented in $@lambda$Prolog, even the parts of
the compiler where implementation in a more traditional language might
have been more convenient (such as register allocation code).

@tt[FreshML] @cite[PG00] adds to the ML language support for
straightforward encoding of variable bindings and alpha-equivalence
classes.  Our approach differs in several important ways.
Substitution and testing for free occurrences of variables are
explicit operations in @tt[FreshML], while @MetaPRL provides a
convenient implicit syntax for these operations.  Binding names in
@tt[FreshML] are inaccessible, while only the formal parts of @MetaPRL
are prohibited from accessing the names.  Informal portions---such as
code to print debugging messages to the compiler writer, or warning
and error messages to the compiler user---can access the binding
names, which aids development and debugging.  @tt[FreshML] is
primarily an effort to add automation; it does not address the issue
of validation directly.

Previous work has also focused on augmenting compilers with formal
tools.  Instead of trying to split the compiler into a formal part and
a heuristic part, one can attempt to treat the @emph{whole} compiler
as a heuristic adding some external code that would watch over what
the compiler is doing and try to establish the equivalence of the
intermediate and final results.  For example, the work of Necula and
Lee @cite["Nec00,NP98"] has led to effective mechanisms for certifying
the output of compilers (e.g., with respect to type and memory-access
safety), and for verifying that intermediate transformations on the
code preserve its semantics. 
@comment{While these approaches certify the code
and ease the debugging process (errors can be flagged at compile time
rather than at run-time), it is not clear that they simplify the
implementation task.}

There have been efforts to present more functional accounts of assembly as well.
Morrisett @it["et. al."] @cite[MWCG98] developed a typed
assembly language capable of supporting many high-level
programming constructs and proof carrying code.  In this scheme,
well-typed assembly programs cannot ``go wrong.''

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
