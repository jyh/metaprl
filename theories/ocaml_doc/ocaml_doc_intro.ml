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
the OCaml implementation.  In CS134a, we used C (and variants) to
specify processes, monitors, semaphores, device drivers and more.
The topic of CS134a was operating systems, and the C language provides
an appropriate machine model for programming the machine.

For the last part of CS134a, we covered a few of the newer operating
systems, like Mach, Amoeba, Spin, Vino, etc.  One running theme of
these systems is that the operating system @emph{kernel} should be
reduced to minimum functionality; additional functionality is defined
through user modules, or by inserting code into the kernel to be run
in kernel space.

One result of this is that more work is being shifted into the
compiler.  For example, the Spin kernel requires that extensions be
written in Modula-3 so that @emph{safety} is guaranteed by the
compiler.  The Vino system retains the unsafe C compiler, but uses
software fault isolation to guarantee the safety of the inserted
code.  In the Amoeba system, the compiler participates in the
distribution and management of resources.

A shift like this is a natural part of any successful process in
computer science.  In general, the initial effort are focused on
getting a @emph{working} system.  When operating systems were first
being developed, the goal was to provide a safe, generic interface.
the emphasis was on simplicity.  C was developed as a language to make
programming the machine easier, and the control that C allows over the
representation and implementation of programs provided tight
programmer control over the efficiency of programs and utilities.
Another goal of these systems was to provide @emph{portability} for a
limited class of machines.  We now have @emph{working}, generic,
systems.

Later, as a process evolves, it is faced with the standard problems of
growth, technically termed @emph{scalability}.  As operating systems
have evolved, more functionality is added to the kernel, and kernel
sizes continue to grow.  Scalability presents three kinds of problems.

@begin[enumerate]

@item{Problems with managing a growing number of computing resources.
   This includes growth in the number of different kinds of machines
   and hardware devices, as well as collecting @emph{distributed}
   resources into a manageable whole.}

@item{Problems with @emph{designing} a large system. As a system
   grows, it must be divided into managable pieces that distinct
   design teams can tackle.}

@item{Problems @emph{maintaining} an ever-growing system.  Monolithic
   systems increase the amount of effort in maintaining the system,
   because, in the worst case, @emph{every} part of the system must
   evolve together with the entire system.}

@end[enumerate]

Traditional systems, like Linux and Windows have addressed part of the
problem through methods like dynamically linking new functionality
(modules) into a running kernel.  The development of modules can be
performed separately from kernel development.  This technique is
workable if the kernel extensions conform to one of the predefined
interfaces, and if the set of kernel extensions are trusted.  No
support is provided for allowing an arbitrary user to add a new
filesystem, for instance.  In addition, many users needing performance
are frustrated at being required to use a general-purpose,
low-performance system API.

The design language traditional operating systems has evolved as well.
Libraries for threads, process synchronization, and message passing
have been implemented to augment the C/C++ programming languages with
more modern features.  The C design model has been stressed by this
process.  Some examples: threads have been grafted onto its serial
programming model; pointers are not valid on multiple machines in a
distributed system, and programmers have to be careful to copy data
when appropriate; message passing primitives tend to be scattered
through the code, making it difficult to change communication
protocols.

Perhaps the biggest strain has been scaling C programs to extremely
large sizes.  The language and compiler provide only limited support
for enforcing modularity, and in general a new component may
interfere with the parts of an existing system (there are no
guarantees about @emph{safety}).  The machine model provided by C is
not always convenient for expressing high-level data structures, like
filesystems or communication protocols.  C programs tend to be tied
closely with the machine architecture, making it difficult to adapt an
existing program to a new model (say, converting a program that uses
shared-memory to a program using message-passing).

The design problem is hard.  No programming language seems appropriate
for @emph{all} programs; if it were, the language and compiler would
themselves would have problems with scalability.  At present, there is
a pressing need for languages that address specific issues.  The
following are just a few examples.

@begin[itemize]

@item{Languages for @emph{graphics and simulation}, where the
   properties of simulation @emph{models} can be separated from
   numerical algorithms and display representations.}

@item{Languages for large (thousands to millions of processors)
   systems, including distributed databases and compute servers.
   Any distributed system of this magnitude must be tolerant to
   massive failures in parts of the system.}

@item{Languages for real-time systems like automotive, aircraft, and
   space applications.}

@item{Languages for adding functionality @emph{safely} to existing
   systems.}

@end[itemize]

As researchers and developers in computer science, we strive to find
simple elegant solutions to difficult problems.  One route that is
sometimes, but not always, appropriate is to adapt the programming
language to the task at hand.  The language is the basis for
designing, understanding, and maintaining a system.  The function of
the compiler is to help us in the design process by providing
useful functionality, catching errors, and (of course) translating
a source program into a program for a specific machine architecture.

In implementing a compiler, we have to answer two questions.  what is
that language we are compiling?  When language do we use to write the
compiler?  This two are not necessarily the same (although they often
are).  The task of compiling is a process of transformation, and many
representations of the program are used in the process.  The compiler
should be implemented in a language where its data structures and
algorithms have the most natural structure.

We'll be using OCaml.  OCaml is a dialect of the ML
(``Meta-Language'') languages, which were designed for the LCF
(``Logic of Computable Functions'') theorem prover.  ML was designed
as a tool for reasoning about programs and languages.  In particular,
it is an ideal language for implementing a compiler.

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
