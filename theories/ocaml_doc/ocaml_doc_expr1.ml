doc <:doc< -*- Mode: text -*-

   @begin[spelling]
   asl asr bool cc chr cmo cmx coercions gdb int lor lsl lsr ml
   doesn ll untyped mod ocamlc
   @end[spelling]

   @begin[doc]
   @chapter[ocaml_doc_expr1]{Simple Expressions}
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2000 Jason Hickey, Caltech

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

doc <:doc< @docoff >>
extends Base_theory

doc <:doc<

@begin[doc]

Many functional programming implementations include a significant
runtime that defines a standard library and a garbage collector.  They
also often include a toploop that can be used to interact with the
system.  OCaml provides a compiler, a runtime, and a toploop.  By
default, the toploop is called @tt[ocaml].  The toploop prints a
prompt (@code{#}), reads an input expression, evaluates it, and prints
the result .  Expressions in the toploop must be terminated by a
double-semicolon @code{;;}.  My machine name is @code{kenai}.

@begin[verbatim]
<kenai 113>ocaml
        Objective Caml version 2.04

# 1 + 4;;
- : int = 5
#
@end[verbatim]

The toploop prints the @emph{type} of the result (in this case,
@code{int}) and the value ($5$).  To exit the toploop, you may type
the end-of-file character (usually Control-D in Unix, and Control-Z in
Windows).

@section[ocaml_doc_expr1]{Basic expressions}

OCaml is a @emph{strongly typed} language: every expression must have
a type, and expressions of one type may not be used as expressions in
another type.  There are no implicit coercions.  Normally, you do not
have to input the types of expressions.  @emph{Type inference}
@cite[DM82] is used to figure out the types for you.

The basic types are @code{unit}, @code{int}, @code{char}, @code{float},
@code{bool}, and @code{string}.

@subsection[ocaml_doc_expr_unit]{@tt{unit}: the singleton type}

The simplest type in OCaml is the @tt{unit} type, which contains one
 element: @code{()}.  This seems to be a rather silly type.  In a functional
language every function must return a value; unit
is commonly used as the value of a procedure that computes by
side-effect.  It corresponds to the @code{void} type in C.

@subsection[ocaml_doc_expr_int]{@tt{int}: the integers}

The @code{int} type is the type of signed integers: $@ldots, -2, -1,
0, 1, 2, @ldots$.  The precision is finite.  On a 32-bit machine
architecture, the precision is 31 bits (one bit is reserved for use by
the runtime), and on a 64-bit architecture, the precision is
63 bits.

There are the usual expressions on integers
@target[ocaml_doc_expr_plus]{+} (addition),
@target[ocaml_doc_expr_minus]{-} (subtraction),
@target[ocaml_doc_expr_star]{*} (multiplication),
@target[ocaml_doc_expr_div]{/} (division), and
@target[ocaml_doc_expr_mod]{@tt{mod}} (remainder).
In addition there are the normal shifting and masking operators on the
binary representations of the numbers.

@begin[itemize]

@item{$i$ @target[ocaml_doc_expr_lsl]{@tt{lsl}} $j$: logical shift left $i @cdot 2^{j}$.}

@item{$i$ @target[ocaml_doc_expr_lsr]{@tt{lsr}} $j$: logical shift right $i @div
   2^{j}$ ($i$ is treated as an unsigned twos-complement number).}

@item{$i$ @target[ocaml_doc_expr_asr]{@tt{asl}} $j$: arithmetic shift
   left $i @cdot 2^{j}$.}

@item{$i$ @target[ocaml_doc_expr_asr]{@tt{asr}} $j$: arithmetic shift right $i @div
   2^{j}$ (the sign of $i$ is preserved).}

@item{$i$ @target[ocaml_doc_expr_land]{@tt{land}} $j$: bitwise-and.}

@item{$i$ @target[ocaml_doc_expr_lor]{@tt{lor}} $j$: bitwise-or.}

@item{$i$ @target[ocaml_doc_expr_lor]{@tt[lxor]} $j$: bitwise exclusive-or.}

@end[itemize]

@subsection[ocaml_doc_expr_float]{@tt{float}: the floating-point numbers}

The floating-point numbers provide fractional numbers.  The syntax of
a floating point includes either a decimal point, or an exponent (base
10) denoted by an E.  A digit is required before the decimal point.
Here are a few examples.

@begin[center]
0.2, 2e7, 3.1415926, 31.415926e-1
@end[center]

The integer arithmetic operators @emph{do not work} with floating
point values.  The corresponding operators include a `.': addition is
@target[ocaml_doc_expr_plusf]{+.}, subtraction is
@target[ocaml_doc_expr_minusf]{-.}, multiplication is
@target[ocaml_doc_expr_starf]{*.}, and division is
@target[ocaml_doc_expr_divf]{/.}.  There are also coercion functions
@target[int_of_float]{@tt{int_of_float}} and
@target[float_of_int]{@tt{float_of_int}}.

@begin[verbatim]
<kenai 114>!!
ocaml
        Objective Caml version 2.04

# 31.415926e-1;;
- : float = 3.1415926
# float_of_int 1;;
- : float = 1
# int_of_float 1.2;;
- : int = 1
# 3.1415926 *. 17.2;;
- : float = 54.03539272
@end[verbatim]

@subsection[ocaml_doc_expr_char]{@tt{char}: the characters}

The character type is implemented as characters from the ASCII
character set.  The syntax for a character constant uses single
quotes.

@begin[center]
@begin[verbatim]
'a', 'Z', '\120', '\t', '\r', '\n'
@end[verbatim]
@end[center]

The numerical specification is in @emph{decimal}, so @code{'\120'} is the
ASCII character @tt{'x'}, not @tt{'P'}.

There are functions for converting between characters and integers.
The function @target[char_code]{@tt{Char.code}} returns the integer
corresponding to a character, and @target[chr]{@tt{Char.chr}} returns
the character with the given ASCII code.  The
@target[lowercase]{@tt["Char.lowercase"]} and
@target[uppercase]{@tt["Char.uppercase"]} functions give the equivalent
lower- or upper-case characters.

@subsection[ocaml_doc_expr_string]{@tt{string}: character strings}

Character strings are a built-in type.  Unlike strings in C, character
strings are not arrays of characters, and they do not use
@code{'\000'} as a termination character.  The
@target[string_length]{@tt{String.length}} function computes the
length of the string.  The syntax for strings uses double-quotes.
Characters in the string may use the @code{\ddd} syntax.

@begin[center]
@begin[verbatim]
"Hello", " world\000 is not a terminator\n", ""
@end[verbatim]
@end[center]

The @code{^} operator performs string concatenation.

@begin[verbatim]
# "Hello " ^ "world\000Not a terminator\n";;
- : string = "Hello world\000Not a terminator\n"
# Lm_printf.printf "%s" ("Hello " ^ "world\000Not a terminator\n");;
Hello worldNot a terminator
- : unit = ()
@end[verbatim]

Strings also allow random access.  The @code{s.[i]} operator gets
character $i$ from string $s$, and the command @code{s.[i] <- c}
replaces character $i$ in string $s$ by character $c$.

@subsection[ocaml_doc_expr_bool]{@tt{bool}: the Boolean values}

There are only two Boolean values: @tt{true} and @tt{false}.  Every
relation returns a Boolean value.  Logical negation is
performed by the @tt{not} function.  The standard binary relations
take two values of equal types and compare them in the normal way.

@begin[itemize]
@item{$x = y$: equality}
@item{$x <> y$: $x$ is not equal to $y$}
@item{$x < y$: $x$ is less than $y$}
@item{$x <= y$: $x$ is no more than $y$}
@item{$x >= y$: $x$ is no less than $y$}
@item{$x > y$: $x$ is greater than $y$}
@end[itemize]

These relations operate on values of @emph{arbitrary} type.  For the
base types in this chapter, the comparison is what you would expect.
For values of other types, the value is implementation-dependent.

The logical operators are also defined: @code{&&} is conjunction, and
@code{||} is disjunction.  Both operators are the ``short-circuit''
versions: the second clause is not evaluated if the result can be
determined from the first clause.  For example, in the following
expression, the clause $3 > 4$ is not evaluated (which makes no
difference at this point, but will make a difference when we add
side-effects).

@begin[verbatim]
# 1 < 2 || 3 > 4;;
- : bool = true
@end[verbatim]

There is also a conditional operator @tt{if $b$ then $e_1$ else
$e_2$}.

@begin[verbatim]
# if 1 < 2 then
     3 + 7
  else
     4;;
- : int = 10
@end[verbatim]

@section[ocaml_compiling]{Compiling your code}

If you wish to compile your code, you should place it in a file with
the @tt{.ml} suffix.  There are two compilers: @tt[ocamlc] compiles to
byte-code, and @tt[ocamlopt] compiles to native machine code.  The
native code is roughly three times faster, but compile time is
longer.  The usage is similar to @tt{cc}.  The double-semicolon
terminators are not necessary in the source files; you may omit them
if the source text is unambiguous.

@begin[itemize]
@item{To compile a single file, use @tt{ocamlc -g -c @emph{file}.ml}.
This will produce a file @tt{@emph{file}.cmo}.  The @tt[ocamlopt]
programs produces a file @tt{@emph{file}.cmx}.  The @code{-g} option
includes debugging information in the output file.}

@item{To link together several files into a single executable, use
@tt[ocamlc] to link the @tt{.cmo} files.  Normally, you would also
specify the @tt{-o @emph{program_file}} option to specify the output
file (the default is @tt{a.out}).  for example, if you have to program
files @tt{x.cmo} and @tt{y.cmo}, the command would be:

@begin[center]
@begin[verbatim]
<kenai 165>ocamlc -g -o program x.cmo y.cmo
<kenai 166>./program
...
@end[verbatim]
@end[center]}
@end[itemize]

There is also a debugger @tt[ocamldebug] that you can use to debug
your programs.  The usage is a lot like @tt{gdb}, with one major
exception: execution can go backwards.  The @tt{back} command will
go back one instruction.

@section[ocaml_type_system]{The OCaml type system}

The ML languages are @emph{strictly} typed.  In addition, every
expression has a exactly one type.  In contrast, C is a weakly-typed
language: values of one type can be coerced to a value of any other
type, whether the coercion makes sense or not.  Lisp is not an
explicitly typed
language: the compiler (or interpreter) will accept any program that
is syntactically correct; the types are checked at run time.  The type
system is not necessarily related to safety: both Lisp and ML are
@emph{safe} languages, while C is not.

What is ``safety?''  There is a formal definition based on the
operational semantics of the programming language, but an approximate
definition is that a valid program will never fault because of an
invalid machine operation.  All memory accesses will be valid.  ML
guarantees safety by guaranteeing that every correctly-typed value is
valid, and Lisp guarantees it by checking for validity at run
time.  One surprising (some would say annoying) consequence is
that ML has no @emph{nil} values; again, all correctly type values are
valid.

As you learn OCaml, you will initially spend a lot of time getting the
OCaml type checker to accept your programs.  Be patient, you will
eventually find that the type checker is one of your best friends.  It
will help you figure out which programs are bogus.  If you make a
change, the type checker will help track down all the parts of your
program that are affected.

In the meantime, here are some rules about type checking.

@begin[enumerate]

@item{Every expression has exactly one type.}

@item{When an expression is evaluated, one of four things may happen:

   @begin[enumerate]
   @item{it may evaluate to a @emph{value} of the same type as the
      expression,}
   @item{it may raise an exception (we'll discuss exceptions in
      Chapter @refchapter[exceptions]),}
   @item{it may not terminate,}
   @item{it may exit.}
   @end[enumerate]}

@end[enumerate]

One of the important points here is that there are no ``pure
commands.''  Even assignments produce a value (although the value has
the trivial @tt{unit} type).

To begin to see how this works, let's look at the conditional
expression.

@begin[verbatim]
<kenai 229>cat -b x.ml
    1	if 1 < 2 then
    2	   1
    3	else
    4	   1.3
<kenai 230>ocamlc -c x.ml
File "x.ml", line 4, characters 3-6:
This expression has type float but is here used with type int
@end[verbatim]

This error message seems rather cryptic: it says that there is a type
error on line 4, characters 3-6 (the expression @tt{1.3}).  The
conditional expression evaluates the test.  If the test is @tt{true},
it evaluates the first branch.  Otherwise, it evaluates the second branch.
In general, the compiler doesn't try to figure out the value of the
test during type checking.  Instead, it requires that both branches of
the conditional have the same type (so that the value will have the same
type no matter how the test turns out).  Since the expressions @tt[1]
and @tt{1.3} have different types, the type checker generates an
error.

One other issue: the @tt{else} branch is not required in a conditional.
If it is omitted, the conditional is treated as if the @tt{else} case
returns the @tt{()} value.  The following code has a type error.

@begin[verbatim]
<kenai 236>cat -b y.ml
    1	if 1 < 2 then
    2	   1
<kenai 237>ocamlc -c y.ml
File "y.ml", line 2, characters 3-4:
This expression has type int but is here used with type unit
@end[verbatim]

In this case, the expression @tt[1] is flagged as a type error,
because it does not have the same type as the omitted @tt{else}
branch.

@section[ocaml_doc_comments]{Comment convention}

In OCaml, comments are enclosed in matching @tt{({}*} and @tt{*{})}
pairs.  Comments may be nested, and the comment is treated
as white space.

   @end[doc]
   @docoff
>>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
