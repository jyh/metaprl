doc <:doc< -*- Mode: text -*-

   @spelling{coercions doesn ll}

   @begin[doc]
   @chapter["ocaml-doc-expr1"]{Simple Expressions}
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
runtime environment that defines a standard library and a garbage
collector.  They also often include a toploop evaluator that can be used to
interact with the system.  OCaml provides a compiler, a runtime, and a
toploop.  By default, the toploop is called @tt[ocaml].  The toploop
prints a prompt (@code{#}), reads an input expression, evaluates it,
and prints the result .  Expressions in the toploop are terminated by
a double-semicolon `@code{;;}'.

@begin[iverbatim]
% ocaml
        Objective Caml version 3.08.0

# 1 + 4;;
- : int = 5
#
@end[iverbatim]

The toploop prints the @emph{type} of the result (in this case,
@code{int}) and the value ($5$).  To exit the toploop, you may type
the end-of-file character (usually Control-D in Unix, and Control-Z in
Microsoft Windows).

@section["ocaml-doc-comments"]{Comment convention}

In OCaml, comments are enclosed in matching @tt{({}*} and @tt{*{})}
pairs.  Comments may be nested, and the comment is treated
as white space.

@section["ocaml-doc-expr1"]{Basic expressions}

OCaml is a @emph{strongly typed} language.  In OCaml every valid
expression must have a type, and expressions of one type may not be
used as expressions in another type.  Apart from polymorphism, which
we discuss in Chapter @refchapter[polymorphism], there are no implicit
coercions.  Normally, you do not have to specify the types of
expressions.  OCaml uses @emph{type inference} @cite[DM82] to figure
out the types for you.

The primitive types are @code{unit}, @code{int}, @code{char}, @code{float},
@code{bool}, and @code{string}.

@subsection["ocaml-doc-expr-unit"]{@tt{unit}: the singleton type}

The simplest type in OCaml is the @tt{unit} type, which contains one
element: @code{()}.  This type seems to be a rather silly.  However,
in a functional language every function must return a value; @code{()} is
commonly used as the value of a procedure that computes by
side-effect.  It corresponds to the @code{void} type in C.

@subsection["ocaml-doc-expr-int"]{@tt{int}: the integers}

The @code{int} type is the type of signed integers: $@ldots, -2, -1,
0, 1, 2, @ldots$ The precision is finite.  Integer values are
represented by a machine word, minus one bit that is reserved for use
by the garbage collector, so on a 32-bit machine architecture, the
precision is 31 bits (one bit is reserved for use by the runtime), and
on a 64-bit architecture, the precision is 63 bits.

Integers are usually specified in decimal, but there are several
alternate forms.  In the following table the symbol $d$ denotes a
decimal digit (`@code{0}'..`@code{9}'); $o$ denotes an octal digit
(`@code{0}'..`@code{7}'); $b$ denotes a binary digit (`@code{0}' or
`@code{1}'); and $h$ denotes a hexadecimal digit
(`@code{0}'..`@code{9}', or `@code{a}'..`@code{f}', or
`@code{A}'..`@code{F}').

@begin[quote]
@begin[tabular,ll]
@line{{$ddd@ldots$}{an @code{int} specified in decimal.}}
@line{{@code{0o}$ooo@ldots$}{an @code{int} specified in octal.}}
@line{{@code{0b}$bbb@ldots$}{an @code{int} specified in binary.}}
@line{{@code{0x}$hhh@ldots$}{an @code{int} specified in hexadecimal.}}
@end[tabular]
@end[quote]

@noindent
There are the usual operations on @code{int}s, including arithmetic
and bitwise operations.

@begin[quote]
@begin[tabular,ll]
@line{{@target["ocaml-doc-expr-neg"]{@tt{-}}$i$ or @code{~-}$i$}{negation.}}
@line{{$i$ @target["ocaml-doc-expr-add"]{@tt{+}} $j$}{addition.}}
@line{{$i$ @target["ocaml-doc-expr-sub"]{@tt{-}} $j$}{subtraction.}}
@line{{$i$ @target["ocaml-doc-expr-mul"]{@tt{*}} $j$}{multiplication.}}
@line{{$i$ @target["ocaml-doc-expr-div"]{@tt{/}} $j$}{division.}}
@line{{$i$ @target["ocaml-doc-expr-mod"]{@tt{mod}} $j$}{remainder.}}

@line{{@target["ocaml-doc-expr-lnot"]{@tt{lnot}} $i$}{bitwise-inverse.}}
@line{{$i$ @target["ocaml-doc-expr-lsl"]{@tt{lsl}} $j$}{logical shift left $i @cdot 2^{j}$.}}

@line{{$i$ @target["ocaml-doc-expr-lsr"]{@tt{lsr}} $j$}{logical shift right $i @div
   2^{j}$ ($i$ is treated as an unsigned twos-complement number).}}

@line{{$i$ @target["ocaml-doc-expr-asr"]{@tt{asl}} $j$}{arithmetic shift
   left $i @cdot 2^{j}$.}}

@line{{$i$ @target["ocaml-doc-expr-asr"]{@tt{asr}} $j$}{arithmetic shift right $@lfloor i @div
   2^{j} @rfloor$ (the sign of $i$ is preserved).}}

@line{{$i$ @target["ocaml-doc-expr-land"]{@tt{land}} $j$}{bitwise-and.}}

@line{{$i$ @target["ocaml-doc-expr-lor"]{@tt{lor}} $j$}{bitwise-or.}}

@line{{$i$ @target["ocaml-doc-expr-lxor"]{@tt[lxor]} $j$}{bitwise exclusive-or.}}

@end[tabular]
@end[quote]

@noindent
The precedences of the integer operators are as follows, listed in increasing order.

@begin[quote]
@begin[tabular,"l|l"]
@line{{Operators}{Associativity}}
@hline
@line{{@tt{+}, @tt{-}}               {left}}
@line{{@tt{*}, @tt{/}, @tt{mod}, @tt{land}, @tt{lor}, @tt{lxor}} {left}}
@line{{@tt{lsl}, @tt{lsr}, @tt{asr}} {right}}
@line{{@tt{lnot}}                    {left}}
@line{{@code{~-}, @tt{-}}              {right}}
@end[tabular]
@end[quote]

@begin[iverbatim]
# 0b1100;;
- : int = 12
# 3 + 4 * 5;;
- : int = 23
# 0x100 lsl (2 + 6);;
- : int = 65536
@end[verbatim]

@subsection["ocaml-doc-expr-float"]{@tt{float}: the floating-point numbers}

The floating-point numbers provide dynamically scaled ``floating
point'' numbers.  The syntax of a floating point includes either a
decimal point, or an exponent (base 10) denoted by an `@code{E}' or
`@code{e}'.  A digit is required before the decimal point.  Here are a
few examples:

@begin[center]
0.2, 2e7, 3.1415926, 31.415926E-1
@end[center]

The integer arithmetic operators (@code{+}, @code{-}, @code{*},
@code{/}, $@ldots$) @emph{do not work} with floating point values.
The corresponding operators include a `.' as follows:

@begin[quote]
@begin[tabular,ll]
@line{{@target["ocaml-doc-expr-negf"]{@tt{-.}}$x$ or @code{~-.}$x$} {floating-point negation}}
@line{{$x$ @target["ocaml-doc-expr-plusf"]{@tt{+.}} $y$}{floating-point addition.}}
@line{{$x$ @target["ocaml-doc-expr-minusf"]{@tt{-.}} $y$}{floating-point subtraction.}}
@line{{$x$ @target["ocaml-doc-expr-starf"]{@tt{*.}} $y$}{float-point multiplication.}}
@line{{$x$ @target["ocaml-doc-expr-divf"]{@tt{/.}} $y$}{floating-point division.}}
@line{{@target["int-of-float"]{@tt{int_of_float}} $x$}{@code{float} to @code{int} conversion.}}
@line{{@target["float-of-int"]{@tt{float_of_int}} $i$}{@code{int} to @code{float} conversion.}}
@end[tabular]
@end[quote]

@begin[iverbatim]
# 31.415926e-1;;
- : float = 3.1415926
# float_of_int 1;;
- : float = 1.
# int_of_float 1.2;;
- : int = 1
# 3.1415926 *. 17.2;;
- : float = 54.03539272
# 1 + 2.0;;
Characters 4-7:
  1 + 2.0;;
      ^^^
This expression has type float but is here used with type int
@end[iverbatim]

The final expression fails to typecheck because the @code{int} operator
@code{+} is used with the floating-point value @code{2.0}.

@subsection["ocaml-doc-expr-char"]{@tt{char}: the characters}

The character type @code{char} specifies characters from the ASCII
character set.  The syntax for a character constants uses the single
quote symbol @code{'}$c$@code{'}.

@begin[iverbatim]
'a', 'Z', ' ', 'W'
@end[iverbatim]

@noindent
In addition, there are several kinds of escape sequences with an alternate syntax.
Each escape sequence begins with the backslash character `@code{\}'.

@begin[quote]
@begin[tabular,ll]
@line{{@code{'\\'}}{The backslash character itself.}}
@line{{@code{'\''}}{The single-quote character.}}
@line{{@code{'\t'}}{The tab character.}}
@line{{@code{'\r'}}{The carraige-return character.}}
@line{{@code{'\n'}}{The newline character.}}
@line{{@code{'\b'}}{The backspace character.}}
@line{{@code{'\}$ddd$@code{'}}{A decimal escape sequence.}}
@line{{@code{'\x}$hh$@code{'}}{A hexadecimal escape sequence.}}
@end[tabular]
@end[quote]

@noindent

A decimal escape sequence must have exactly three decimal characters
$d$, and specifies the ASCII character with the specified decimal
code.  A hexadecimal escape sequence must have exactly two hexadecimal
characters $h$.

@begin[iverbatim]
'a', 'Z', '\120', '\t', '\n', '\x7e'
@end[iverbatim]

There are functions for converting between characters and integers.
The function @target["char-code"]{@tt{Char.code}} returns the integer
corresponding to a character, and @target[chr]{@tt{Char.chr}} returns
the character with the given ASCII code.  The
@target[lowercase]{@tt["Char.lowercase"]} and
@target[uppercase]{@tt["Char.uppercase"]} functions give the equivalent
lower- or upper-case characters.

@begin[iverbatim]
# '\120';;
- : char = 'x'
# Char.code 'x';;
- : int = 120
# '\x7e';;
- : char = '~'
# Char.uppercase 'z';;
- : char = 'Z'
# Char.uppercase '[';;
- : char = '['
# Char.chr 32;;
- : char = ' '
@end[verbatim]

@subsection["ocaml-doc-expr-string"]{@tt{string}: character strings}

In OCaml, character strings belong to a primitive type @code{string}.
Unlike strings in C, character strings are not arrays of characters,
and they do not use the null-character @code{'\000'} for termination.

The syntax for strings uses the double-quote symbol `@code{"}' as
a delimiter.  Characters in the string may use the escape sequences
defined for characters.

@begin[center]
@begin[iverbatim]
"Hello", "The character '\000' is not a terminator", "\072\105"
@end[iverbatim]
@end[center]

@noindent
The @code{^} operator performs string concatenation.

@begin[iverbatim]
# "Hello " ^ " world\n";;
- : string = "Hello world\n"
# "The character '\000' is not a terminator";;
- : string = "The character '\000' is not a terminator"
# "\072\105";;
- : string = "Hi"
@end[iverbatim]

Strings also allow random access.  The expression @code{s.[i]} returns
the $i$'th from string $s$; and the expression @code{s.[i] <- c}
replaces the $i$'th in string $s$ by character $c$, returing a
@code{unit} value.  The @target[String]{@tt{String}} module (see
Section @refsection["ocaml-doc-string"]) also defines many functions
to manipulate strings, including the
@target[string_length]{@tt{String.length}} function, which returns the
length of a string; and the @target[string_sub]{@tt{String.sub}}
function, which returns a substring.

@begin[iverbatim]
# "Hello".[1];;
- : char = 'e'
# "Hello".[0] <- 'h';;
- : unit = ()
# String.length "Abcd\000";;
- : int = 5
# String.sub "Ab\000cd" 1 3;;
- : string = "b\000c"
@end[verbatim]

@subsection["ocaml-doc-expr-bool"]{@tt{bool}: the Boolean values}

The @code{bool} type is used to represent the Boolean values @tt{true}
and @tt{false}.  Logical negation of Boolean values is performed by
the @tt{not} function.

There are several relations that can be used to compare values,
returning @code{true} if the comparison holds and @code{false}
otherwise.

@begin[quote]
@begin[tabular,ll]
@line{{$x$ @code{=}  $y$}{$x$ is equal to $y$.}}
@line{{$x$ @code{==} $y$}{$x$ is ``identical'' to $y$.}}
@line{{$x$ @code{<>} $y$}{$x$ is not equal to $y$.}}
@line{{$x$ @code{<}  $y$}{$x$ is less than $y$.}}
@line{{$x$ @code{<=} $y$}{$x$ is no more than $y$.}}
@line{{$x$ @code{>=} $y$}{$x$ is no less than $y$.}}
@line{{$x$ @code{>}  $y$}{$x$ is greater than $y$.}}
@end[tabular]
@end[quote]

These relations operate on two values $x$ and $y$ having equal but
arbitrary type.  For the primitive types in this chapter, the
comparison is what you would expect.  For values of other types, the
value is implementation-dependent, and in some cases may raise a
runtime error.  For example, functions (discussed in the next chapter)
cannot be compared.

The @code{==} deserves special mention, since we use the word
``identical'' in an informal sense.  The exact semantics is this: if
the expression ``$x$ @code{==} $y$'' evaluates to @code{true}, then so
does the expression ``$x$ @code{=} $y$''.  However it is still
possible for ``$x$ @code{=} $y$'' to be @code{true} even if ``$x$
@code{==} $y$'' is not.  In the OCaml implementation from INRIA, the
expression ``$x$ @code{==} $y$'' evaluates to @code{true} only if the two
values $x$ and $y$ are exactly the same value.  The comparison
@code{==} is a constant-time operation that runs in a bounded number
of machine instructions; the comparison @code{=} is not.

@begin[iverbatim]
# 2 < 4;;
- : bool = true
# "A good job" > "All the tea in China";;
- : bool = false
# 2 + 6 = 8;;
- : bool = true
# 1.0 = 1.0;;
- : bool = true
# 1.0 == 1.0;;
- : bool = false
# 2 == 1 + 1;;
- : bool = true
@end[verbatim]

Strings are compared lexicographically (in alphabetical-order), so the
second example is @code{false} because the character `@code{l}' is
greater than the space-character `@code{ }' in the ASCII character
set.  The comparison ``@code{1.0 == 1.0}'' in this case returns
@code{false} (because the 2 floating-point numbers were typed
separately), but it performs normal comparison on @code{int} values.

There are two logical operators: @code{&&} is conjunction (and), and
@code{||} is disjunction (or).  Both operators are the
``short-circuit'' versions: the second clause is not evaluated if the
result can be determined from the first clause.

@begin[iverbatim]
# 1 < 2 || (1 / 0) > 0;;
- : bool = true
# 1 < 2 && (1 / 0) > 0;;
Exception: Division_by_zero.
# 1 > 2 && (1 / 0) > 0;;
- : bool = false
@end[iverbatim]

@noindent Conditionals are expressed with the syntax @tt{if $b$ then
$e_1$ else $e_2$}.

@begin[iverbatim]
# if 1 < 2 then
     3 + 7
  else
     4;;
- : int = 10
@end[iverbatim]

@section["ocaml-core-precedences"]{Operator precedences}

The precedences of the operators in this section are as follows,
listed in increasing order.

@begin[quote]
@begin[tabular,"l|l"]
@line{{Operators}{Associativity}}
@hline
@line{{@code{||}} {left}}
@line{{@code{&&}} {left}}
@line{{@code{=}, @code{==}, @code{!=}, @code{<>}, @code{<}, @code{<=}, @code{>}, @code{>=}} {left}}
@line{{@tt{+}, @tt{-}, @tt{+.}, @tt{-.}}               {left}}
@line{{@tt{*}, @tt{/}, @tt{*.}, @tt{/.}, @tt{mod}, @tt{land}, @tt{lor}, @tt{lxor}} {left}}
@line{{@tt{lsl}, @tt{lsr}, @tt{asr}} {right}}
@line{{@tt{lnot}}                    {left}}
@line{{@code{~-}, @tt{-}, @code{~-.}, @tt{-.}}              {right}}
@end[tabular]
@end[quote]

@section["ocaml-type-system"]{The OCaml type system}

The ML languages are statically and strictly typed.  In addition, every
expression has a exactly one type.  In contrast, C is a weakly-typed
language: values of one type can usually be coerced to a value of any
other type, whether the coercion makes sense or not.  Lisp is not a
statically typed language: the compiler (or interpreter) will accept
any program that is syntactically correct; the types are checked at
run time.  The type system is not necessarily related to safety: both
Lisp and ML are @emph{safe} languages, while C is not.

What is ``safety?''  There is a formal definition based on the
operational semantics of the programming language, but an approximate
definition is that a valid program will never fault because of an
invalid machine operation.  All memory accesses will be valid.  ML
guarantees safety by proving that every program that passes the type
checker can never produce a machine fault, and Lisp guarantees it by
checking for validity at run time.  One surprising (some would say
annoying) consequence is that ML has no @code{nil} or @code{NULL}
values; these would potentially cause machine errors if used where
a value is expected.

As you learn OCaml, you will initially spend a lot of time getting the
OCaml type checker to accept your programs.  Be patient, you will
eventually find that the type checker is one of your best friends.  It
will help you figure out where errors may be lurking in your programs.
If you make a change, the type checker will help track down the parts
of your program that are affected.

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

@begin[iverbatim]
<kenai 229>cat -b x.ml
    1	if 1 < 2 then
    2	   1
    3	else
    4	   1.3
<kenai 230>ocamlc -c x.ml
File "x.ml", line 4, characters 3-6:
This expression has type float but is here used with type int
@end[iverbatim]

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

@begin[iverbatim]
% cat -b y.ml
    1	if 1 < 2 then
    2	   1
% ocamlc -c y.ml
File "y.ml", line 2, characters 3-4:
This expression has type int but is here used with type unit
@end[iverbatim]

In this case, the expression @tt[1] is flagged as a type error,
because it does not have the same type as the omitted @tt{else}
branch.

@section["ocaml-compiling"]{Compiling your code}

You aren't required to use the toploop for all your programs.  In
fact, as your programs become larger, you will begin to use the
toploop less, and rely more on the OCaml compilers.  Here is a brief
introduction to using the compiler; more information is given in the
Chapter @refchapter[files].

If you wish to compile your code, you should place it in a file with
the @tt{.ml} suffix.  In INRIA OCaml, there are two compilers:
@tt[ocamlc] compiles to byte-code, and @tt[ocamlopt] compiles to
native machine code.  The native code is several times faster, but
compile time is longer.  The usage is similar to @tt{cc}.  The
double-semicolon terminators are not necessary in @code{.ml} source
files; you may omit them if the source text is unambiguous.

@begin[itemize]

@item{{To compile a single file, use @tt{ocamlc -g -c
@emph{file}.ml}.  This will produce a file @tt{@emph{file}.cmo}.  The
@tt[ocamlopt] programs produces a file @tt{@emph{file}.cmx}.  The
@tt{-g} option is valid only for @tt{ocamlc}; it causes debugging
information to be included in the output file.}}

@item{To link together several files into a single executable, use
@tt[ocamlc] to link the @tt{.cmo} files.  Normally, you would also
specify the @tt{-o @emph{program_file}} option to specify the output
file (the default is @tt{a.out}).  For example, if you have two program
files @tt{x.cmo} and @tt{y.cmo}, the command would be:

@begin[iverbatim]
% ocamlc -g -o program x.cmo y.cmo
% ./program
...
@end[iverbatim]}
@end[itemize]

There is also a debugger @tt[ocamldebug] that you can use to debug
your programs.  The usage is a lot like @tt{gdb}, with one major
exception: execution can go backwards.  The @tt{back} command will
go back one instruction.

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
