(* -*- mode: text; -*- *)
doc <:doc<
   @begin[spelling]
   CPS ML Mojave compilable Necula Liang HOAS FDL Girard Moggi Plotkin Sabry Wadler Morrisett
   @end[spelling]

   @chapter[m_doc_compiler_fdl]{Logical frameworks and the FDL}
   @section[m_doc_intro_fdl]{Introduction}

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}
   Modified By:
   @end[license]
>>
extends M_doc_comment

doc <:doc<

A @emph{logical framework} is a system that allows the definition and
use of @emph{multiple} logics, supporting derivation in any of the
logics that are defined.  We take the term logic in its general
meaning.  A logic may characterize a very large domain, like
arithmetic, or it may characterize a smaller domain, like compilation,
abstract algebra, graph theory, or any other computational,
algorithmic domain.  The @MetaPRL logical programming environment is
an augmented logical framework that supporting reductions and
relations between logics, as well as the embedding of one domain
within another.  @MetaPRL is a modular system, organizing and
collecting knowledge in a hierarchy that corresponds closely to
standard practice in software engineering.

The FDL is an ideal companion in this enterprise, because it captures,
stores, and indexes the knowledge from these domains.  This allows a
programmer to search for knowledge and algorithms from any of the
contributions to the library.  The FDL and @MetaPRL provide an
instance of a system that cooperates to proved the programmer with a
rich source of algorithmic knowledge, as well as a state-of-the-art
means to organize and incorporate that knowledge into software
systems.

In this chapter, we describe the development of a new class of
algorithms using the @MetaPRL/FDL system.  Our goal has two parts: 1)
to contribute new algorithmic content to the FDL, and 2) demonstrate
how the logical framework is used to organize and develop the
knowledge during the software development process.  We organize this
as a case study for the development of several important, fundamental
algorithms that are widely used in the programming language and
compiler community.  We develop this case study as far as an
implementation of a complete compiler that uses the algorithms that we
develop.

The text for this chapter is generated from source code of this
project.  That is, this document is part of the formal content that is
stored and generated as part of the FDL.  By doing so, we connect the
documentation directly to the source that provides the algorithmic
knowledge in the FDL.

@subsection[fdl_motivation]{Compilers and programming languages}

One of the areas that has plagued the programming language community
is the problem of compiler validation.  The task of designing and
implementing a compiler can be difficult even for a small language.
There are many phases in the translation from source to machine code,
and an error in any one of these phases can alter the semantics of the
generated program.

There are two main reasons to validate the compiler.  First, if there
is an error in the compiler, then there is no assurance that the
properties specified by the programmer are valid at runtime.  Second,
if the compiler is validated, it becomes possible to certify mobile
code.  That is, source-level proofs provided by the programmer can be
translated automatically to runtime proofs that accompany the code and
can be validated by the recipient.

In initial work (with a Caltech undergraduate) @cite[AGH02], we
explored the feasibility of using a formal system to reason about the
internal compiler representations for a program.  More recently
@cite[HNGA03], we developed an alternative approach, based on the use
of higher-order abstract syntax @cite["NH02,PE88"] and term rewriting
to construct an entire compiler in MetaPRL.  All program
transformations, from parsing to code generation, are cleanly isolated
and specified as term rewrites.

There are many advantages to using a formal system.  The most
important is that the correctness of the compiler is dependent only on
the rewriting rules that provide the formal part of the translation.
The vast majority of compiler code does not have to be trusted.  In
our current work, the correctness of the compiler depends on less than
1% of its code.  In addition, we find that in many cases it is
@emph{easier} to implement the compiler because the logical framework
provides a great deal of automation.

Compilers make use of many fundamental algorithms used to transform
and analyze programs.  For example, CPS (continuation-passing style)
transformation is a widely-used algorithm that transforms the control
flow of a program.  As Sabry and Wadler show @cite[SW97], Plotkin's
CPS translation @cite[Plo75], Moggi's monadic translation
@cite[Mog88], and Girard's translation to linear logic @cite[Gir87a]
are all related; insight into any one of these translations provides
insight into all three.  While CPS transformation may be fundamental,
it is an example of an algorithm that is difficult for humans to
understand, and it is quite difficult to perform by hand.  The payoff
for a general formalization as part of the FDL is thus quite high.

Other widely-used algorithms include closure conversion (where
functions in a program are lifted to top-level), code generation,
register allocation, including spill selection.  Instances of these
algorithms are used widely is many areas of computer science,
especially for compilers for languages ranging from Lisp and ML, to
Java, C, C#, etc.  By defining them as part of the FDL, we provide a
freely-available formal implementation that serves as a common
reference for the many applications that use these algorithms.

Our approach is based on the use of higher-order abstract syntax
@cite["NH02,PE88"] and term rewriting in a general-purpose logical
framework that uses the FDL.  All program transformations, from
parsing to code generation, are cleanly isolated and specified as term
rewrites.  In our system, term rewrites specify an equivalence between
two code fragments that is valid in any context.  Rewrites are
bidirectional and neither imply nor presuppose any particular order of
application.  Rewrite application is guided by programs in the
meta-language of the logical framework.

The correctness of the compiler is dependent only on the rewriting
rules.  Programs that guide the application of rewrites do not have to
be trusted because they are required to use rewrites for all program
transformations.  If the rules can be validated against a program
semantics, and if the compiler produces a program, that program will
be correct relative to those semantics.  The role of the guidance
programs is to ensure that rewrites are applied in the appropriate
order so that the output of the compiler contains only assembly.

The collection of rewrites needed to implement a compiler is small
(hundreds of lines of formal mathematics) compared to the entire code
base of a typical compiler (often more than tens of thousands of lines
of code in a general-purpose programming language).  Validation of the
former set is clearly easier.  Even if the rewrite rules are not
validated, it becomes easier to assign accountability to individual
rules.

The use of a @MetaPRL and the FDL has another major advantage that we
explore in this paper: in many cases it is @emph{easier} to implement
the compiler, for several reasons.  The terminology of rewrites
corresponds closely to mathematical descriptions frequently used in
the literature, decreasing time from concept to implementation.

In this chapter, we explore these problems and show that formal
compiler development is feasible, perhaps easy using the @MetaPRL/FDL
system.  This chapter is organized around a case study, where we
develop a compiler that generates Intel x86 machine code for an
ML-like language using the @MetaPRL logical framework
@cite["HNC+03,Hic01,MPHome"].  The compiler is fully implemented and
online as part of the Mojave research project @cite[MojaveHome].

@subsection[organization]{Organization}

The translation from source code to assembly is usually done in three
major stages.  The parsing phase translates a source file (a sequence
of characters) into an abstract syntax tree; the abstract syntax is
translated to an intermediate representation; and the intermediate
representation is translated to machine code.  The reason for the
intermediate representation is that many of the transformations in the
compiler can be stated abstractly, independent of the source and
machine representations.

The language that we are using as an example (see Section
@refsection[m_doc_parsing]) is a small language similar to ML
@cite[Ull98].  To keep the presentation simple, the language is
untyped.  However, it includes higher-order and nested functions, and
one necessary step in the compilation process is closure conversion,
in which the program is modified so that all functions are closed.

The high-level outline of the paper includes the following sections:
{Section  @refsection[m_doc_parsing]}  {Parsing},
{Section  @refsection[m_doc_ir]}       {Intermediate representation (IR)},
{Section  @refsection[m_doc_x86_asm]}  {Intel x86 assembly code generation},
{Section  @refsection[m_doc_summary]}  {Summary and future work},
{Section  @refsection["related-work"]} {Related work}.
Before describing each of these
stages, we first introduce the terminology and syntax of the formal
system in which we define the program rewrites.

@subsection[terminology]{Terminology}

All logical syntax is expressed in the language of @em{terms}.  The
general syntax of all terms has three parts.  Each term has 1) an
operator-name (like ``sum''), which is a unique name identifying the
kind of term; 2) a list of parameters representing constant values; and
3) a set of subterms with possible variable bindings.  We use the
following syntax to describe terms:

$$
@underbrace{@it[opname]; @it{operator@space name}}
@underbrace{{[p_1; @cdots; p_n]}; @it{parameters}}
@underbrace{{@lbrace @vec{v}_1. t_1; @cdots; @vec{v}_m. t_m @rbrace}; @it{subterms}}
$$

@begin[center]
@begin[small]
@begin[tabular,"|c|l|"]
@hline
@line{{Displayed form} {Term}}
@hline
@line{{$1$} @tt{{number[1]@lbrace@rbrace}}}
@line{{$@lambda x. b$} @tt{lambda[]@lbrace x. b @rbrace}}
@line{{$f(a)$} @tt{{apply[] @lbrace f; a @rbrace}}}
@line{{$x + y$} @tt{{sum[]@lbrace x; y @rbrace}}}
@hline
@end[tabular]
@end[small]
@end[center]

A few examples are shown in the table.  Numbers have an integer
parameter.  The @tt{lambda} term contains a binding occurrence: the
variable $x$ is bound in the subterm $b$.

Term rewrites are specified in @MetaPRL using second-order variables,
which explicitly define scoping and substitution @cite[NH02]. A second-order
variable pattern has the form $v[v_1; @cdots; v_n]$, which represents
an arbitrary term that may have free variables $v_1, @ldots, v_n$.
The corresponding substitution has the form $v[t_1; @cdots; t_n]$,
which specifies the simultaneous, capture-avoiding substitution of
terms $t_1, @ldots, t_n$ for $v_1, @ldots, v_n$ in the term matched by
$v$.  For example, the rule for $@beta$-reduction is specified with
the following rewrite.

$$
   @xrewrite[beta]{{(@lambda x. v_1[x])@space v_2}; {v_1[v_2]}}
$$

The left-hand-side of the rewrite is a pattern called
the @emph{redex}.  The $v_1[x]$ stands for an arbitrary term with free
variable $x$, and $v_2$ is another arbitrary term.  The
right-hand-side of the rewrite is called the @emph{contractum}.  The
second-order variable $v_1[v_2]$ substitutes the term matched by $v_2$
for $x$ in $v_1$.  A term rewrite specifies that any term that matches
the redex can be replaced with the contractum, and vice-versa.

Rewrites that are expressed with second-order notation are strictly
more expressive than those that use the traditional substitution
notation.  The following rewrite is valid in second-order notation.

$$
   @xrewrite[const]{{(@lambda x. v[])@space 1}; {(@lambda x. v[])@space 2}}
$$

In the context $@lambda x$, the second-order variable $v[]$ matches
only those terms that do not have $x$ as a free variable.  No
substitution is performed; the $@beta$-reduction of both sides of the
rewrite yields $v[] @longleftrightarrow v[]$, which is valid
reflexively.  Normally, when a second-order variable $v[]$ has an
empty free-variable set $[]$, we omit the brackets and use the simpler
notation $v$.


@MetaPRL is a tactic-based prover that uses @OCaml @cite[Caml99] as
its meta-language.  When a rewrite is defined in @MetaPRL, the
framework creates an @OCaml expression that can be used to apply the
rewrite.  Code to guide the application of rewrites is written in
@OCaml, using a rich set of primitives provided by @MetaPRL.  @MetaPRL
automates the construction of most guidance code; we describe rewrite
strategies only when necessary.  For clarity, we will describe syntax
and rewrites using the displayed forms of terms.

The compilation process is expressed in @MetaPRL as a judgment of
the form ${@Gamma @vdash @compilable{e}}$, which states the the
program $e$ is compilable in any logical context $@Gamma$.  The
meaning of the $@compilable{e}$ judgment is defined by the target
architecture.  A program $e'$ is compilable if it is a sequence of
valid assembly instructions.  The compilation task is a process of
rewriting the source program $e$ to an equivalent assembly program
$e'$.

@docoff
>>


(*
 * -*-
 * Local Variables:
 * fill-column: 70
 * End:
 * -*-
 *)
