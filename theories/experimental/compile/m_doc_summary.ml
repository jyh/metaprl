(* -*- mode: text; -*- *)
doc <:doc<
   @begin[spelling]
   CPS grunge Liang Morrisett Necula untrusted Hannan LF Pfenning Pnueli Resler Singerman Danvy
   Fellinski HOAS compilable
   @end[spelling]

   @section[m_doc_summary]{Summary and Future Work}

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
extends M_doc_comment
extends M_doc_cps

doc <:doc<

One of the points we have stressed in this presentation is that the implementation of formal
compilers is easy, perhaps easier than traditional compiler development using a general-purpose
language.  This case study presents a convincing argument based on the authors' previous
experience implementing compilers using traditional methods.  The formal process was easier to specify
and implement, and @MetaPRL provided a great deal of automation for frequently occurring tasks.  In
most cases, the implementation of a new compiler phase meant only the development of new rewrite
rules.  There is very little of the ``grunge'' code that plagues traditional implementations, such
as the maintenance of tables that keep track of the variables in scope, code-walking procedures to
apply a transformation to the program's subterms, and other kinds of housekeeping code.

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
register allocator.  Preliminary tests suggest that performance of programs generated from the
formal compiler is comparable,
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
programming languages. We are currently working on the construction of a compiler for a @emph{typed}
language, using sequent notation to address the problem of retaining higher order abstract syntax in
the definition of mutually recursive functions.

In the compiler presented in this paper we took a very conservative approach to making sure the
the rule rewrite transformations do not affect the program semantics. A very good example of this is
the CPS transformation (Section @refsection[m_doc_cps]). There we have defined the semantics of the
$@CPS{c;e}$ to just be the function $c$ applied to expression $e$. Under this semantics, the rule
@tt[cps_prog] (that states that a program is compilable if the result of its CPS transformation is
compilable) is obviously valid --- if we take $c$ to be an identity function, then under this
semantics the rule simply does not change the program. This semantics also provides us with
sufficient information to be able to separately validate each individual CPS-related program
transformation.

A downside of such a conservative approach is that it becomes very hard to write transformations in
an optimal way. In particular, the CPS rewrites presented is this paper introduce a large number of
``administrative'' beta-redices that would need to be eliminated in subsequent optimization stages.
We can chose an alternative approach where
the CPS term is defined as performing a syntactical transformation of a program. In this approach,
all the rewrites for the CPS term become simply parts of the @emph{definition} of the CPS
transformation. All the work required to prove that the transformation does not change the meaning
of the program goes into establishing that the corresponding @tt[cps_prog] rule is valid. This
approach makes it much easier to specify the CPS transformation in an optimal way, following the
approach of Danvy and Fellinski @cite[DF92]. We currently use this approach in our work-in-progress
compiler @cite["GHNT04,HNG05"]; the specification of the CPS transformation ends up being even
simpler than Danvy and Fellinski's because of the efficiency of the HOAS language that we use.

This paper can be considered to be a first step in a much larger project. One of our main goals for
this step was to investigate the feasibility of this approach in a small case study. We believe that
we have demonstrated that at least on this level the approach we propose is definitely feasible. In
fact, almost every time the reality of this work did not match our expectations it was because this
approach turned out to be @emph{easier} than we have originally anticipated. Now that this case
study have demonstrated the feasibility of this approach @emph{in principle}, we have moved on to
implementing a more realistic compiler for a strongly-typed ML-like language @cite["GHNT04,HNG05"].

This second-generation formal compiler is already implemented, for the most part. In addition to
taking advantage of the lessons learned in this case study (such as using Danvy an Fellinski's
approach to CPS and using nested sequents @cite[GHNT04] to represent recursive functions), one of
the main goals of the second-generation compiler work was to explore the issues of @emph{modularity}
and @emph{feature isolation}. This goal was successfully achieved as well --- we were able to
structure the compiler in such a way that different language features are cleanly isolated and
experimentation with one of the language features can not break compilation of unrelated features.

The fact that in our approach all the program transformations are @emph{individually} semantics
preserving, together with feature isolation and modularity of the second-generation compiler makes
our compilers readily amenable to incremental verification (including both on-paper verification
and computer-aided formal proofs). While verification was not among the goals of our compiler case
studies, it is among the gaols of the larger project. It is also one of our larger goals to explore
formally the issues of correctness and programming language meta-theory.  In a related
effort @cite[NKYH05], we are investigating the use of reflection as a means for meta-reasoning
about formal artifacts.  We expect that reflection will provide a generic mechanism for
automatically internalizing the artifacts specified in a prover, including those presented here, and
programming language meta-theory in general.

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

Hannan and Pfenning @cite[HP92] constructed a verified compiler in LF (as realized in the Elf
programming language) for the untyped lambda calculus and a variant of the CAM @cite[CCM87] runtime.
This work formalizes both compiler transformation and verifications as deductive systems, and
verification is against an operational semantics.

Previous work has also focused on augmenting compilers with formal
tools.  Instead of trying to split the compiler into a formal part and
a heuristic part, one can attempt to treat the @emph{whole} compiler
as a heuristic adding some external code that would watch over what
the compiler is doing and try to establish the equivalence of the
intermediate and final results.  For example, the work of Necula and
Lee @cite["Nec00,NP98"] has led to effective mechanisms for certifying
the output of compilers (e.g., with respect to type and memory-access
safety), and for verifying that intermediate transformations on the
code preserve its semantics.  Pnueli, Siegel, and Singerman @cite[PSS98] perform verification in a
similar way, not by validating the compiler, but by validating the result of a transformation using
simulation-based reasoning.

Semantics-directed compilation @cite[Lee89] is aimed at allowing language designers to generate
compilers from high-level semantic specifications.  Although it has some overlap with our work, it
does not address the issue of trust in the compiler.  No proof is generated to accompany the
compiler, and the compiler generator must be trusted if the generated compiler is to be trusted.

Boyle, Resler, and Winter @cite[BRW97], outline an approach to building trusted compilers that is
similar to our own.  Like us, they propose using rewrites to transform code during compilation.
Winter develops this further in the HATS system @cite[Win99] with a special-purpose transformation
grammar.  An advantage of this approach is that the transformation language can be tailored for the
compilation process.  However, this significantly restricts the generality of the approach, and
limits re-use of existing methods and tools.

There have been efforts to present more functional accounts of assembly as well.
Morrisett @it["et. al."] @cite[MWCG98] developed a typed
assembly language capable of supporting many high-level
programming constructs and proof carrying code.  In this scheme,
well-typed assembly programs cannot ``go wrong.''

@docoff
>>

(*
 * -*-
 * Local Variables:
 * fill-column: 100
 * End:
 * -*-
 *)
