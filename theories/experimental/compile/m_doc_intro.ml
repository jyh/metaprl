doc <:doc< -*- mode: text; -*-
   @begin[spelling]
   CPS ML Mojave untrusted compilable Necula Liang HOAS
   Morrisett
   @end[spelling]
  
   @begin[doc]
   @section[m_doc_intro]{Introduction}
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
  
   Author: Jason Hickey @email{jyh@cs.caltech.edu}
   Modified By: 
   @end[license]
>>
extends M_doc_comment

doc <:doc< 
@begin[doc]

The task of designing and implementing a compiler can be difficult
even for a small language.  There are many phases in the translation
from source to machine code, and an error in any one of these phases
can alter the semantics of the generated program.  The use of
programming languages that provide type safety, pattern matching, and
automatic storage management can reduce the compiler's code size and
eliminate some common kinds of errors.  However, many programming
languages that appear well-suited for compiler implementation, like ML
@cite[Ull98], still do not address other issues, such as substitution
and preservation of scoping in the compiled program.

In this paper, we present an alternative approach, based on the use of
higher-order abstract syntax @cite["NH02,PE88"] and term rewriting in
a general-purpose logical framework.  All program transformations,
from parsing to code generation, are cleanly isolated and specified as
term rewrites.  In our system, term rewrites specify an equivalence
between two code fragments that is valid in any context.  Rewrites are
bidirectional and neither imply nor presuppose any particular order of
application.  Rewrite application is guided by programs in the
meta-language of the logical framework.

There are many advantages to using formal rewrites.  Program scoping
and substitution are managed implicitly by the logical framework; it
is not possible to specify a program transformation that modifies the
program scope.  Perhaps most importantly, the correctness of the
compiler is dependent only on the rewriting rules.  Programs that
guide the application of rewrites do not have to be trusted because
they are required to use rewrites for all program transformations.  If
the rules can be validated against a program semantics, and if the
compiler produces a program, that program will be correct relative to
those semantics.  The role of the guidance programs is to ensure that
rewrites are applied in the appropriate order so that the output of
the compiler contains only assembly.

The collection of rewrites needed to implement a compiler is small
(hundreds of lines of formal mathematics) compared to the entire code
base of a typical compiler (often more than tens of thousands of lines
of code in a general-purpose programming language).  Validation of the
former set is clearly easier.  Even if the rewrite rules are not
validated, it becomes easier to assign accountability to individual
rules.

The use of a logical framework has another major advantage that we
explore in this paper: in many cases it is @emph{easier} to implement
the compiler, for several reasons.  The terminology of rewrites
corresponds closely to mathematical descriptions frequently used in
the literature, decreasing time from concept to implementation.  The
logical framework provides a great deal of automation, including
efficient substitution and automatic $@alpha$-renaming of variables to
avoid capture, as well as a large selection of rewrite strategies to
guide the application of program transformations.  The compilation
task is phrased as a theorem-proving problem, and the logical
framework provides a means to examine and debug the effects of the
compilation process interactively.  The facilities for automation and
examination establish an environment where it is easy to experiment
with new program transformations and extensions to the compiler.

In fairness, formal compilation also has potential disadvantages.  The
use of higher-order abstract syntax, in which variables in the
programming language are represented as variables in the logical
language, means that variables cannot be manipulated directly in the
formal system; operations that modify the program scope, such as
capturing substitution, are difficult if not impossible to express
formally.  In addition, global program transformations, in which
several parts of a program are modified simultaneously, can sometimes
be difficult to express with term rewriting.

The most significant impact of using a formal system is that program
representations must permit a substitution semantics.  Put another
way, the logical framework requires the development of
@emph{functional} intermediate representations, where heap locations
may be mutable, but variables are not.  This potentially has a major
effect on the formalization of imperative languages, including
assembly language, where registers are no longer mutable.  This
seeming contradiction can be resolved, as we show in the second half
of this paper, but it does require a departure from the majority of
the literature on compilation methods.

In this paper, we explore these problems and show that formal compiler
development is feasible, perhaps easy.  We do not specifically address
the problem of compiler verification in this paper; our main objective
is to develop the models and methods needed during the compilation
process.  The format of this paper is organized around a case study,
where we develop a compiler that generates Intel x86 machine code for
an ML-like language using the @MetaPRL logical framework
@cite["HNC+03,Hic01,MPHome"].  The compiler is fully implemented and
online as part of the Mojave research project @cite[MojaveHome].
This document is generated from the program sources (@MetaPRL provides
a form of literate programming), and the complete source code is
available online at @url["http://metaprl.org/"] as well as in the
technical report.

@subsection[organization]{Organization}

The translation from source code to assembly is usually done in three major stages.  The parsing
phase translates a source file (a sequence of characters) into an abstract syntax tree; the abstract
syntax is translated to an intermediate representation; and the intermediate representation is
translated to machine code.  The reason for the intermediate representation is that many of the
transformations in the compiler can be stated abstractly, independent of the source and machine
representations.

The language that we are using as an example (see Section
@refsection[m_doc_parsing]) is a small language similar to ML
@cite[Ull98].  To keep the presentation simple, the language is
untyped.  However, it includes higher-order and nested functions, and
one necessary step in the compilation process is closure conversion,
in which the program is modified so that all functions are closed.
The high-level outline of the paper is as follows.

@begin[center]
@begin[tabular,lll]
@line{$@bullet$ {Section  @refsection[m_doc_parsing]} {parsing}}
@line{$@bullet$ {Section  @refsection[m_doc_ir]}      {intermediate representation (IR)}}
@line{$@bullet$ {Section  @refsection[m_doc_x86_asm]} {Intel x86 assembly code generation}}
@line{$@bullet$ {Section  @refsection["related-work"]} {Related work}}
@end[tabular]
@end[center]

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

$$@xrewrite[beta]{{(@lambda x. v_1[x])@space v_2}; {v_1[v_2]}}$$

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

$$@xrewrite[const]{{(@lambda x. v[])@space 1}; {(@lambda x. v[])@space 2}}$$

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
@end[doc]
>>


(*
 * -*-
 * Local Variables:
 * fill-column: 70
 * End:
 * -*-
 *)
