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

Like other dialects of ML, OCaml includes an expressive polymorphic
type system, type inference, pattern matching, and automatic storage
management.  In addition, OCaml is the only widely-available dialect
of ML that has an object system.

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

There are problems with taking too strong a stance in favor
of functional programming.  One is that every updatable data structure
has to be passed as an argument to every function that uses it (this
is called ``threading'' the state).  This can make the code obscure if
there are too many of these data structures.  We take a moderate
approach.  Imperative code may be used where it is natural, but
imperative code @emph{may not} be used if there is a more elegant
functional version.

@section[ocaml_doc_intro_organization]{Organization}

This document is organized as a @emph{user guide} to programming in
OCaml.  It is not a reference manual: there is already an online
reference manual.  I assume that you have programming experience in an
imperative language like C; I'll point out the differences between ML
and C in the cases that seem appropriate.

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
