(*! -*- Mode: text -*-
 *
 * @begin[spelling]
 * API CS LCF ML Monolithic Scalability Vino rec scalability
 * stance filesystems ll gcd managable updatable
 * @end[spelling]
 *
 * @begin[doc]
 * @chapter[ocaml_doc_intro]{Introduction}
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2000 Jason Hickey, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)

(*! @docoff *)
extends Base_theory

(*!
@begin[doc]

This document is an introduction to ML programming, specifically for
the Objective Caml (@emph{OCaml}) programming language from INRIA
@cite["leroy:ocaml,remy:ocaml"].  OCaml is a dialect of the ML
(@emph{Meta-Language}) family of languages, which derive from the
Classic ML language designed by Robin Milner in 1975 for the LCF
(@emph{Logic of Computable Functions}) theorem prover
@cite["lcf,GMW79"].

OCaml shares many features with other dialects of ML, and it provides
several new features of its own.  Throughout this document, we use the
term ML to stand for any of the dialects of ML, and OCaml when a
feature is specific to OCaml.

@begin[itemize]
@item{{ML is a @bf{functional} language, meaning that functions are
treated as first-class values.  Functions may be nested, functions may
be passed as arguments to other functions, and functions can be stored
in data-structures.  Functions are treated like their mathematical
counterparts as much as possible.  Assignment statements that
permanently change the value of an expression are permitted, but used
much less frequently than in languages like C or Java.}}

@item{{
ML is @bf{strongly typed}, meaning that the type of every variable
and every expression in a program is determined at compile-time.
Programs that pass the type checker are @emph{safe}: they will never
``go wrong'' because of an illegal instruction or memory fault.}}

@item{{
Related to strong typing, ML uses @bf{type inference} to infer
types for the expressions in a program.  Even though the language is
strongly typed, it is rare that the programmer ever has to annotate a
program with type constraints.}}

@item{{
The ML type system is @bf{polymorphic}, meaning that it is possible
to write programs that work for values of any type.  For example, it
is straightforward to define data structures like lists, stacks, and
trees that can contain elements of any type.  In a language like C or
Java, the programmer would either have to write different
implementations for each type (say, lists of integers vs. lists of
floating-point values), or else use explicit coercions to bypass the
type system.}}

@item{{
ML implements an @bf{pattern matching} mechanism that
unifies case analysis and data destructors.}}

@item{{
ML includes an expressive @bf{module system} that allows data
structures to be specified and defined @emph{abstractly}.  The module
system includes @emph{functors}, which are are functions over modules
that can be used to produce one data structure from another.}}

@item{{
OCaml also the only widely-available ML implementation to include an
@bf{object system}.  The module system and object system complement
one another: the module system provides data abstraction, and the
object system provides inheritance and re-use.}}

@item{{
OCaml includes a compiler that supports @bf{separate compilation}.
This makes that the development process easier by reducing the amount
of code that must be recompiled when a program is modified.  OCaml
actually includes two compilers: a @emph{byte-code} compiler that
produces code for the portable OCaml byte-code interpreter, and an
@emph{native-code} compiler that produces efficient code for many
machine architectures.}}

@item{{
One other feature should be mentioned: all the languages in the ML
family have a @bf{formal semantics}, which means that programs have a
mathematical interpretation.  While this may not seem to be directly
useful to a programmer, it means that the programming language
constructs are designed to fit together, making the programming
language easier to understand and explain.}}

@end[itemize]

@section[ocaml_doc_intro_functional]{Functional and imperative languages}

The ML languages are ``semi-functional,'' which means that the normal
programming style is functional, but the language includes assignment and
side-effects.

To compare ML with an imperative language, here is how Euclid's
algorithm would normally be written in an imperative language like C.

@begin[verbatim]
/*
* * Determine the greatest common divisor of two positive
* * numbers a and b.  We assume a>b.
* */
int gcd(int a, int b)
{
   int r;

   while(r = a % b) {
      a = b;
      b = r;
   }
   return b;
}
@end[verbatim]

In a language like C, the algorithm is normally implemented as a loop,
and progress is made by modifying the state.  Reasoning about this
program requires that we reason about the program state: give an
invariant for the loop, and show that the state makes progress on each
step toward the goal.

In OCaml, Euclid's algorithm is normally implemented using recursion.
The steps are the same, but there are no side-effects.  The @bf{let}
keyword specifies a definition, the @bf{rec} keyword specifies that
the definition is recursive, and the @tt{gcd a b} defines a function
with two arguments $a$ and $b$.

@begin[verbatim]
let rec gcd a b =
   let r = a mod b in
      if r = 0 then
         b
      else
         gcd b r
@end[verbatim]

In ML, programs rarely use assignment or side-effects except for I/O.
Functional programs have some nice properties: one is that data
structures are @emph{persistent} (by definition), which means that no
data structure is ever destroyed.

There are problems with taking too strong a stance in favor of
functional programming.  One is that every updatable data structure
has to be passed as an argument to every function that uses it (this
is called ``threading'' the state).  This can make the code obscure if
there are too many of these data structures.  We take a moderate
approach.  Imperative code may be used where it is natural, but the
use of imperative code is discouraged if there is a more elegant
functional version.

@section[ocaml_doc_intro_organization]{Organization}

This document is organized as a @emph{user guide} to programming in
OCaml.  It is not a reference manual: there is already an online
reference manual.  I assume that the reader already has some
experience using an imperative programming language like C; I'll point
out the differences between ML and C in the cases that seem
appropriate.

@section[ocaml_doc_intro_additional_source]{Additional Sources of Information}

This document was originally used for a course in compiler
construction at Caltech.  The course material, including exercises, is
available at @tt{http://www.cs.caltech.edu/courses/cs134/cs134b}.

The OCaml reference manual @cite["leroy:ocaml"] is available on the
OCaml home page @tt{http://www.ocaml.org/}.

The author can be reached at @tt{jyh@cs.caltech.edu}.

 * @end[doc]
 *)

(*!
 * @docoff
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
