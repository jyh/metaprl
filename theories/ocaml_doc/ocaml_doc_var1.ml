doc <:doc< -*- Mode: text -*-

   @begin[spelling]
   Obfuscated Ok expr
   @end[spelling]

   @begin[doc]
   @chapter["ocaml-doc-name1"]{Variables and Functions}
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

So far, we have only considered simple expressions not involving
variables. In ML, variables are @emph{names} for values.  In a purely
functional setting, it is not possible to tell the difference between
a variable and the value it stands for.

Variable bindings are introduced with the @tt{let} keyword.
The syntax of a simple top-level declaration is as follows.

@begin[center]
@tt{let @emph{name} = @emph{expr}}
@end[center]

For example, the following code defines two variables $x$ and $y$ and
adds them together to get a value for $z$.

@begin[iverbatim]
# let x = 1;;
val x : int = 1
# let y = 2;;
val y : int = 2
# let z = x + y;;
val z : int = 3
@end[iverbatim]

Definitions using @tt{let} can also be nested using the
@tt{in} form.

@begin[center]
@tt{let @emph{name} = @emph{expr1} in @emph{expr2}}
@end[center]

The expression @emph{expr2} is called the @emph{body} of the @tt{let}.
The variable @emph{name} is defined as the value of @emph{expr1}
within the body.  If there is only one definition for @emph{name}, the
variable @emph{name} is defined @emph{only} in the body @emph{expr2}
and not @emph{expr1} (or anywhere else).

Lets with a body are expressions; the value of a @tt{let}
expression is the value of the body.

@begin[iverbatim]
# let x = 1 in
  let y = 2 in
     x + y;;
- : int = 3
# let z =
     let x = 1 in
     let y = 2 in
        x + y;;
val z : int = 3
@end[iverbatim]

Binding is @emph{static} (lexical scoping): if there is more than one
definition for a variable, the value of the variable is defined by the
most recent @tt{let} definition for the variable.  The variable is
bound only in the body of the let; or, for toplevel definitions, the
rest of the file.

@begin[iverbatim]
# let x = 1 in
  let x = 2 in
  let y = x + x in
     x + y;;
- : int = 6
@end[iverbatim]

What is the value of $z$ in the following definition?

@begin[iverbatim]
# let x = 1;;
val x : int = 1
# let z =
     let x = 2 in
     let x = x + x in
        x + x;;
val z : int = 8
# x;;
- : int = 1
@end[iverbatim]

@section["ocaml-doc-functions"]{Functions}

Functions are defined with the @tt{fun} keyword.  The @tt{fun} is
followed by a sequence of variables that name the arguments, the
@code{->} separator, and then the body of the function.  By default,
functions are not @emph{named}.  In ML, functions are values like any
other.  They may be constructed, passed as arguments, and applied to
arguments.  Like any other value, they may be named by using
a @tt{let}.

@begin[verbatim]
# let incr = fun i -> i + 1;;
val incr : int -> int = <fun>
@end[verbatim]

Note the type @code{int -> int} for the function.  The @code{->} is
for a @emph{function type}.  The type before the arrow is the type of
the function's argument, and the type after the arrow is the type of
the result.  The @tt[incr] function takes an integer argument, and
returns an integer.

The syntax for function application (function call) is concatenation:
the function is followed by its arguments.  The precedence of function
application is higher than most operators.  Parentheses are needed for
arguments that are not simple expressions.

@begin[iverbatim]
# incr 2;;
- : int = 3
# incr 2 * 3;;
- : int = 9
# incr (2 * 3);;
- : int = 7
@end[iverbatim]

Functions may also be defined with multiple arguments.  For example,
a function to compute the sum of two integers can be defined as follows.

@begin[iverbatim]
# let sum = fun i j -> i + j;;
val sum : int -> int -> int = <fun>
# sum 3 4;;
- : int = 7
@end[iverbatim]

Note the @emph{type} for @tt{sum}: @code{int -> int -> int}.  The
arrow associates to the right, so this could also be written @code{int
-> (int -> int)}.  That is, @tt{sum} is a function that takes a single
integer argument, and returns a function that takes another integer
argument and returns an integer.  Strictly speaking, all functions in
ML take a single argument; multiple-argument functions are implemented
as @emph{nested} functions (this is called ``Currying'', after Haskell
Curry, a famous logician who had a significant impact on the design
and interpretation of programming languages).  The definition of
@tt{sum} above is equivalent to the following explicitly-curried
definition.

@begin[iverbatim]
# let sum = (fun i -> (fun j -> i + j));;
val sum : int -> int -> int = <fun>
@end[iverbatim]

The application of @tt{sum} to only one argument is called a ``partial
application.''

@begin[iverbatim]
# let incr = sum 1;;
val incr : int -> int = <fun>
# incr 5;;
- : int = 6
@end[iverbatim]

Since named functions are so common, OCaml provides an alternate
syntax for functions using a @tt{let} definition.  The formal
parameters of the function are listed after to the function name,
before the equality symbol.

@begin[iverbatim]
# let sum i j =
     i + j;;
val sum : int -> int -> int = <fun>
@end[iverbatim]

@subsection["ocaml-doc-scoping"]{Scoping and nested functions}

Functions may be arbitrarily nested.  They may also be defined and
passed as arguments.  The rule for scoping uses static binding: the
value of a variable is determined by the code in which a function is
defined---not by the code in which a function is evaluated.  For
example, another way to define @tt{sum} is as follows.

@begin[iverbatim]
# let sum i =
     let sum2 j =
        i + j
     in
        sum2;;
val sum : int -> int -> int = <fun>
# sum 3 4;;
- : int = 7
@end[iverbatim]

@noindent
To illustrate the scoping rules, let's consider the following
definition.

@begin[iverbatim]
# let i = 5;;
val i : int = 5
# let addi j =
     i + j;;
val addi : int -> int = <fun>
# let i = 7;;
val i : int = 7
# addi 3;;
- : val = 8
@end[iverbatim]

In the @tt[addi] function, the value of @tt{i} is defined by the
previous definition of @tt{i} as 5.  The second definition of @tt{i}
has no effect on the definition for @tt[addi], and the application of
@tt[addi] to the argument 3 results in $3 + 5 = 8$.

@subsection["ocaml-doc-recursive-functions"]{Recursive functions}

Suppose we want to define a recursive function: that is, a function
that is used in its own function body.  In functional languages,
recursion is used to express repetition and looping.  For example, the
``power'' function that computes $x^i$ would be defined as follows.

@begin[iverbatim]
# let rec power i x =
     if i = 0 then
        1.0
     else
        x *. (power (i - 1) x);;
val power : int -> float -> float = <fun>
# power 5 2.0;;
- : float = 32
@end[iverbatim]

Note the use of the @tt[rec] modifier after the @tt{let} keyword.
Normally, the function is @bf{not} defined in its own body.  The
following definition is very different.

@begin[iverbatim]
# let power_broken i x =
     (float_of_int i) +. x;;
val power_broken : int -> float -> float = <fun>
# let power_broken i x =
     if i = 0 then
        1.0
     else
        x *. (power_broken (i - 1) x);;
val power_broken : int -> float -> float = <fun>
# power_broken 5 2.0;;
- : float = 12
@end[iverbatim]

Mutually recursive definitions (functions that call one another) can
be defined using the @tt{and} keyword to connect several @tt{let}
definitions.

@begin[iverbatim]
# let rec f i j =
     if i = 0 then
        j
     else
        g (j - 1)
  and g j =
     if j mod 3 = 0 then
        j
     else
        f (j - 1) j;;
val f : int -> int -> int = <fun>
val g : int -> int = <fun>
# g 5;;
- : int = 3
@end[iverbatim]

@subsection["ocaml-doc-hof"]{Higher order functions}

Let's consider a definition where a function is passed as an
argument, and another function is returned.  Given an arbitrary
function $f$ on the real numbers, a numerical derivative is defined
approximately as follows.

@begin[iverbatim]
# let dx = 1e-10;;
val dx : float = 1e-10
# let deriv f =
     (fun x -> (f (x +. dx) -. f x) /. dx);;
val deriv : (float -> float) -> float -> float = <fun>
@end[iverbatim]

Remember, the arrow associates to the right, so another way to write
the type is @code{(float -> float) -> (float -> float)}.  That is, the
derivative is a function that takes a function as an argument, and
returns a function.

Let's apply this to the @tt{power} function defined above, partially
applied to the argument 3.

@begin[iverbatim]
# let f = power 3;;
val f : float -> float = <fun>
# f 10.0;;
- : float = 1000
# let f' = deriv f;;
val f' : float -> float = <fun>
# f' 10.0;;
- : float = 300.000237985
# f' 5.0;;
- : float = 75.0000594962
# f' 1.0;;
- : float = 3.00000024822
@end[iverbatim]

As we would expect, the derivative of $x^3$ is approximately $3x^2$.
To get the second derivative, we apply the @tt[deriv] function to
@code{f'}.

@begin[iverbatim]
# let f'' = deriv f';;
val f'' : float -> float = <fun>
# f'' 0.0;;
- : float = 6e-10
# f'' 1.0;;
- : float = 0
# f'' 10.0;;
- : float = 0
@end[iverbatim]

The second derivative, which we would expect to be $6x$, is way off!
Ok, there are some numerical errors here.  Don't expect functional
programming to solve all your problems.

@begin[iverbatim]
# let g x = 3.0 *. x *. x;;
val g : float -> float = <fun>
# let g' = deriv g;;
val g' : float -> float = <fun>
# g' 1.0;;
- : float = 6.00000049644
# g' 10.0;;
- : float = 59.9999339101
@end[iverbatim]

@section["ocaml-doc-naming"]{Variable names}

As you may have noticed in the previous section, the @bf{'} character
is a valid character in a variable name.  In general, a variable name
may contain letters (lower and upper case), digits, and the @bf{'} and
@bf{_} characters. but @bf{it must} begin with a lowercase letter or
the underscore character, and it may not the the @bf{_} all by itself.

In OCaml, sequences of characters from the infix operators, like
@code{+, -, *, /, ...} are also valid names.  The normal prefix
version is obtained by enclosing them in parentheses.  For example,
the following code is a proper entry for the Obfuscated ML contest.
Don't use this code in class.

@begin[iverbatim]
# let (+) = ( * )
  and (-) = (+)
  and ( * ) = (/)
  and (/) = (-);;
val + : int -> int -> int = <fun>
val - : int -> int -> int = <fun>
val * : int -> int -> int = <fun>
val / : int -> int -> int = <fun>
# 5 + 4 / 1;;
- : int = 15
@end[iverbatim]

Note that the @tt{*} operator requires space within the parenthesis.
This is because of comment conventions: comments start with
@tt{({}*} and end with @tt{*{})}.

The redefinition of infix operators may make sense in some contexts.
For example, a program module that defines arithmetic over complex
numbers may wish to redefine the arithmetic operators.  It is also
sensible to add new infix operators.  For example, we may wish to have
an infix operator for the @tt{power} construction.

@begin[iverbatim]
# let ( ** ) x i = power i x;;
val ** : float -> int -> float = <fun>
# 10.0 ** 5;;
- : float = 100000
@end[iverbatim]

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
