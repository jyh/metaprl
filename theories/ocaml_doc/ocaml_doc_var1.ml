(*!
 * @begin[spelling]
 * Obfuscated Ok expr incr rec toplevel
 * @end[spelling]
 *
 * @begin[doc]
 * @chapter[ocaml_doc_name1]{Variables and Functions}
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
include Base_theory

(*!
 * @begin[doc]

So far, we have only considered simple expressions, not involving
variables.  In ML, variables are @emph{names} for values.  In a purely
functional setting, it is not possible to tell the difference between
a variable from the value it stands for.

In OCaml, variable bindings are introduced with the @tt{let} keyword.
The syntax of a simple top-level declaration is a follows.

@begin[center]
@tt{let @emph{name} = @emph{expr}}
@end[center]

For example, the following code defines two variables $x$ and $y$ and
adds them together to get a value for $z$.

@begin[verbatim]
# let x = 1;;
val x : int = 1
# let y = 2;;
val y : int = 2
# let z = x + y;;
val z : int = 3
@end[verbatim]

Definitions using @tt{let} can also be nested arbitrarily using the
@tt{in} form.

@begin[verbatim]
# let x = 1 in
  let y = 2 in
     x + y;;
- : int = 3
# let z =
     let x = 1 in
     let y = 2 in
        x + y;;
val z : int = 3
@end[verbatim]

Binding is @emph{static} (lexical scoping): the value of a variable is
defined by the innermost @tt{let} definition for the variable.  The
variable is bound only in the body of the let; or, for toplevel
definitions, the rest of the file.

@begin[verbatim]
# let x = 1 in
  let x = 2 in
  let y = x + x in
  x + y;;
- : int = 6
@end[verbatim]

What is the value of $z$ in the following definition?

@begin[verbatim]
# let x = 1
  let z =
     let x = 2 in
     let x = x + x in
        x + x
@end[verbatim]

@section[ocaml_doc_functions]{Functions}

Functions are defined with the @tt{fun} keyword.  The @tt{fun} is
followed by a sequence of variables that name the arguments, the
@code{->} separator, and then the body of the function.  By default,
functions are not @emph{named}.  In ML, functions are values like any
other.  They may be constructed, passed as arguments, and applied to
specific arguments.  Like any other value, they may be named by using
a @tt{let}.

@begin[verbatim]
# let incr = fun i -> i + 1;;
val incr : int -> int = <fun>
@end[verbatim]

The @code{->} is a @emph{function type}.  The type before the arrow is
the type of the function's argument, and the value after the arrow is
the type of the value.  The @tt{incr} function takes an integer
argument, and returns an integer.

The syntax for function application (function call) is concatenation:
the function is followed by its arguments.

@begin[verbatim]
# incr 2;;
- : int = 3
@end[verbatim]

Functions may also be defined with multiple arguments.  For example,
the sum of two integers might be defined as follows.

@begin[verbatim]
# let sum = fun i j -> i + j;;
val sum : int -> int -> int = <fun>
# sum 3 4;;
- : int = 7
@end[verbatim]

Note the @emph{type} of the sum: @code{int -> int -> int}.  The arrow
associates to the right, so this could also be written
@code{int -> (int -> int)}.  That is, the @tt{sum} is a function that
takes a single integer argument, and returns a function that takes
another integer argument and returns an integer.  Strictly speaking,
all functions in ML take a single argument; multiple-argument
functions are implemented as @emph{nested} functions.  The application
of a function to only some of its arguments is called a ``partial
application.''

@begin[verbatim]
# let incr = sum 1;;
val incr : int -> int = <fun>
# incr 5;;
- : int = 6
@end[verbatim]

Since named functions are so common, OCaml provides an alternate
syntax for functions using a @tt{let} definition.  The formal
parameters of the function are listed next to the function name,
before the equality.

@begin[verbatim]
# let sum i j =
     i + j;;
val sum : int -> int -> int = <fun>
@end[verbatim]

@subsection[ocaml_doc_scoping]{Scoping and nested functions}

In ML, functions may be arbitrarily nested.  They may also be defined
and passed as arguments.  The rule for scoping uses static binding:
the value of a variable is determined by the code in which a function
is defined---not by the code in which a function is evaluated.  All
arguments, and @tt{let}-bound variables are visible in nested
functions.  For example, another way to define the summation is as
follows.

@begin[verbatim]
# let sum i =
     let sum2 j =
        i + j
     in
        sum2;;
val sum : int -> int -> int = <fun>
# sum 3 4;;
- : int = 7
@end[verbatim]

To illustrate the scoping rules, let's consider the following
definition.

@begin[verbatim]
# let sum i j =
     let apply f k =
        f k
     in
     let i = 5 in
     let sum2 l =
        i + l
     in
        apply sum2 j;;
val sum : 'a -> int -> int = <fun>
@end[verbatim]

You can ignore the @code{'a} type for the moment.  What is the value
of this function?  The @tt{apply} function takes a function @tt{f} and
an argument @tt{j}, and it applies @tt{f} to @tt{j}.  In the next
step, @tt{i} is bound to $5$.  In @tt{sum2}, is the value of @tt{i} 5,
or is it determined by the formal parameter @tt{i}.  Trying this out
we find the following.

@begin[verbatim]
# sum 3 10;;
- : int = 15
@end[verbatim]

Apparently, the value of @tt{i} is 5, not 3 as we passed in the
argument.  Static (lexical) scoping determines this: the value of
@tt{i} in @tt{sum2} must be 5, because the closest definition of
@tt{i} is 5---even though @tt{sum2} is evaluated within the @tt{apply}
function where the value of @tt{i} is determined by the argument $i$.

@subsection[ocaml_doc_recursive_functions]{Recursive functions}

Suppose we want to define a recursive function: that is, a function
where the function is used in its own function body.  In functional
languages, recursion is used to express repetition and looping.  For
example, the ``power'' function that computes $x^i$ would be
defined as follows.

@begin[verbatim]
# let rec power i x =
     if i = 0 then
        1
     else
        x *. (power (i - 1) x);;
val power : int -> float -> float = <fun>
# power 5 2.0;;
- : float = 32
@end[verbatim]

Note the use of the @tt{rec} modifier after the @tt{let} keyword.
Normally, the function is @bf{not} defined in its own body.  The
following definition is very different (note the use of the type
variables @code{'a} and @code{'b}, which we describe in the section on
polymorphic types).

@begin[verbatim]
# let power i x =
     x;;
val power : 'a -> 'b -> 'b = <fun>
# let power i x =
     if i = 0 then
        1
     else
        x *. (power (i - 1) x);;
val power : int -> float -> float = <fun>
# power 5 2.0;;
- : float = 4
@end[verbatim]

Mutually recursive definitions (functions that call one another) can
be defined use the @tt{and} keyword to connect several @tt{let}
definitions.

@begin[verbatim]
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
@end[verbatim]

@subsection[ocaml_doc_hof]{Higher order functions}

Let's consider another definition where a function is passed as an
argument, and another function is returned.  Given an arbitrary
function $f$ on the real numbers, a numerical derivative is defined
approximately as follows.

@begin[verbatim]
# let dx = 1e-10;;
val dx : float = 1e-10
# let deriv f =
     (fun x -> (f x +. f (x +. dx)) /. dx);;
val deriv : (float -> float) -> float -> float = <fun>
@end[verbatim]

Remember, the arrow associates to the right, so another way to write
the type is @code{(float -> float) -> (float -> float)}.  That is, the
derivative is a function that takes a function as an argument, and
returns a function.

Let's apply this to the @tt{power} function defined above.

@begin[verbatim]
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
# let f'' = deriv f';;
val f'' : float -> float = <fun>
# f'' 0.0;;
- : float = 6e-10
# f'' 1.0;;
- : float = 0
# f'' 10.0;;
- : float = 0
@end[verbatim]

As we would expect, the derivative of $x^3$ is approximately $3x^2$.
The second derivative, which we would expect to be $6x$, is way off!
Ok, there are some numerical errors here.  Don't expect functional
programming to solve all your problems.

@begin[verbatim]
# let g x = 3.0 *. x *. x;;
val g : float -> float = <fun>
# let g' = deriv g;;
val g' : float -> float = <fun>
# g' 1.0;;
- : float = 6.00000049644
# g' 10.0;;
- : float = 59.9999339101
@end[verbatim]

@section[ocaml_doc_naming]{Variable names}

As you may have noticed in the previous section, the @bf{'} character
is a valid character in a variable name.  In general, a variable name
may contain letters (lower and upper case), digits, and the @bf{'} and
@bf{_} characters. but @bf{it must} begin with a lowercase letter or
the underscore character.

In OCaml, sequences of characters from the infix operators, like
@code{+, -, *, /, ...} are also valid names.  The normal prefix
version is obtained by enclosing them in parenthesis.  For example,
the following code is a proper entry for the Obfuscated ML contest.
Don't use this code in class.

@begin[verbatim]
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
@end[verbatim]

Note that the @tt{*} operator requires space within the parenthesis.
This is because of comment conventions: comments start with
@tt{({}*} and end with @tt{*{})}.

The redefinition of infix operators may make sense in some contexts.
For example, a program module that defines arithmetic over complex
number may wish to redefine the arithmetic operators.  It is also
sensible to add new infix operators.  For example, we may wish to have
an infix operator for the @tt{power} construction.

@begin[verbatim]
# let ( ** ) x i = power i x;;
val ** : float -> int -> float = <fun>
# 10.0 ** 5;;
- : float = 100000
@end[verbatim]

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
