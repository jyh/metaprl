doc <:doc< -*- Mode: text -*-

   @begin[spelling]
   Dereferencing blit bool doesn downto fields int
   jason ll namespace permissable rec ref toplevel
   @end[spelling]

   @begin[doc]
   @chapter[records]{Reference cells, Side-Effects, and Loops}
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

As we have seen, functional programming has one principal
feature---functions are first-class.  Functions may be passed as
arguments, returned as the result of function calls, and stored in
data structures just like any other value.  Indeed, the presence of
first-class functions is the only requirement for a programming
language to be considered functional.  By this definition, many
programming languages are functional, including not only the usual
examples like OCaml, Lisp, and Haskell, but also languages like
Javascript (where functions are associated with fields on a web page),
or even C (where functions are represented with pointers).

Another property of a programming language is purity.  A @emph{pure}
programming language is one without assignment, where variables cannot
be modified by side-effect.  Haskell is an example of a pure
functional programming language; OCaml and most Lisp dialects are
impure, meaning that they allow side-effects in some form.  The
motivation for pure functional programming stems in part from their
simplicity and mathematical foundations.  Mathematically speaking, a
function is a single-valued map, meaning that if $f$ is a function and
$f(x)$ is defined, then there is only one value for $f(x)$.  Consider
the following ``counter function,'' written in C.

@begin[iverbatim]
   int count = 0;
   int counter() {
       count = count + 1;
       return count;
   }
@end[iverbatim]

Clearly, this is not a function in the mathematical sense, since the
value returned by the @code{counter} function is different each time
it is called; in fact the expression @code{counter() == counter()}
is always false.

Reasoning about languages with assignment and side-effects is more
difficult than for the pure languages because of the need to specify
the program ``state,'' which defines the values for the variables in
the program.  To be fair, pure languages have issues of their own.  It
isn't always easy to write a pure program that is as efficient as an
impure one.  Furthermore, the world is impure in some sense.  When I
run a program that displays the message ``Hello world'' on my screen,
the display is ultimately modified by side-effect to show the message.

For these reasons, and perhaps others, OCaml is an impure language
that allows side-effects.  However, it should be noted that the
@emph{predominant} style used by OCaml programmers is pure; assignment
and side-effects are used infrequently, if at all.

@section[references]{Reference cells}

The simplest mutable value in OCaml is the @emph{reference cell},
which can be viewed as a ``box'' where the contents can be replaced by
assignment.  Reference cells are created with the @code{ref} function,
which takes an initial value for the cell; they are mutated with
the @code{:=} operator, which assigns a new value to the cell; and they
are dereferenced with the @code{!} operator.

@begin[iverbatim]
# let i = ref 1;;
val i : int ref = {contents = 1}
# i := 2;;
- : unit = ()
# !i;;
- : int = 2
@end[iverbatim]

The built-in type @code{'a ref} is the type of a reference cell.
Don't get confused with the @code{!} operator in C.  The following
code illustrates a potential pitfall.

@begin[iverbatim]
# let flag = ref true;;
val flag : bool ref = {contents=true}
# if !flag then 1 else 2;;
- : int = 1
@end[iverbatim]

If you have programmed in C, you may be tempted to read @code{if !flag
then ...} as testing if the @tt{flag} is false.  This is @emph{not}
the case; the @code{!}  operator is more like the @code{*} operator in
C.

Another key difference between reference cells and assignment in
languages like C is that it is the @emph{cell} that is modified by
assignment, not the variable (variables are always immutable in
OCaml).  For example, in the following code, the two variables $i$ and
$j$ refer to the same reference cell, so an assignment to the cell
affects the value of both variables.

@begin[iverbatim]
# let i = ref 1;;
val i : int ref = {contents = 1}
# let j = i;;
val j : int ref = {contents = 1}
# i := 2;;
- : unit = ()
# !j;;
- : int = 2
@end[iverbatim]

@subsection["ref-value-restriction"]{Value restriction}

As we mentioned in Section @refsection["value-restriction"],
mutability and side-effects interact with type inference.  For
example, consider a ``one-shot'' function that saves a value on its
first call, and returns that value on all future calls.  This function
is not properly polymorphic because it contains a mutable field.  The
following example illustrates the issue.

@begin[iverbatim]
# let x = ref None;;
val x : '_a option ref = {contents=None}
# let one_shot y =
     match !x with
        None ->
           x := Some y;
           y
      | Some z ->
           z;;
val one_shot : '_a -> '_a = <fun>
# one_shot 1;;
- : int = 1
# one_shot;;
val one_shot : int -> int = <fun>
# one_shot 2;;
- : int = 1
# one_shot "Hello";;
Characters 9-16:
This expression has type string but is here used with type int
@end[iverbatim]

The value restriction requires that polymorphism be restricted to
immutable values, including functions, constants, and constructors
with fields that are values.  A function application is @emph{not} a
value, and a reference cell is not a value.  By this definition, the
@tt{x} variable and the @tt{one_shot} function cannot be polymorphic,
as the type constants @code{'_a} indicate.

@subsection["ref-basic"]{Imperative programming and loops}

In an imperative programming language, iteration and looping are used
much more frequently than recursion.  The examples in Figure
@reffigure["imp-fact"] show an example of a C function to compute the
factorial of a number, and a corresponding OCaml program written in
the same style.

@begin[figure,"imp-fact",t]
@begin[center]
@begin[tabular,ll]
@line{{
@begin[minipage,"2.5in",t]
@begin[verbatim]
int fact(int i) {
    int j = 1, k;
    for(k = 2; k <= i; k++)
       j *= k;
    return j;
}
@end[verbatim]
@end[minipage]}

{@begin[minipage,"2.0in",t]
@begin[verbatim]
let fact i =
   let j = ref 1 in
      for k := 2 to i do
         j := !j * k
      done;
      !j
@end[verbatim]
@end[minipage]}}
@end[tabular]
@end[center]
@begin[caption]
Two examples of a factorial function written in an imperative style.
@end[caption]
@end[figure]

A @code{for} loop defines iteration over an integer range.  In the
factorial example, the loop index is @code{k}, the initial value is
@code{2}, the final value is @code{i}.  The loop body is evaluated for
each integer value of @code{k} between @code{2} and @code{i}
@emph{inclusive}.  If @code{i} is less than @code{2}, the loop body is
not evaluated at all.

OCaml also includes a for-loop that iterates downward, specified by
using the keyword @code{downto} instead of @code{to}, as well as a
general @code{while}-loop.  These variations are shown in Figure
@reffigure["imp-fact2"].

@begin[figure,"imp-fact",t]
@begin[center]
@begin[tabular,ll]
@line{{
@begin[minipage,"2.5in",t]
@begin[verbatim]
let fact i =
   let j = ref 1 in
      for k := i downto 2 do
         j := !j * k
      done;
      !j
@end[verbatim]
@end[minipage]}

{@begin[minipage,"2.0in",t]
@begin[verbatim]
let fact i =
   let j = ref 1 in
   let k = ref 2 in
      while !k <= i do
         j := !j * !k
      done;
      !j
@end[verbatim]
@end[minipage]}}
@end[tabular]
@end[center]
@begin[caption]
Two variations on the factorial using a downward-iterating for loop, and a while loop.
@end[caption]
@end[figure]

For the factorial function, there isn't really any reason to use
iteration over recursion, and there are several reasons not to.  For
reference, two pure functional versions of the factorial function are
shown in Figure @reffigure["fun-fact"].  One reason to prefer the pure
functional version is that it is simpler and more clearly expresses
the computation being performed.  While it can be argued what the
properties ``simple'' and ``clear'' are never simple and clear in the
context of programming language, most OCaml programmers would find the
pure functional versions easier to read.

---JYH: need to add a "difficult" section. ---
Another reason is that the pure functional version is likely to be
more efficient because there is no penalty for the overhead of
assigning to and dereferencing reference cells.  In addition, the
compiler is particularly effective in generating code for
tail-recursive functions.  A @emph{tail-recursive} function is a
function where the result is a constant or a call to another function.
The second version of the factorial function in Figure
@reffigure["fun-fact"] is tail-recursive because it returns either the
constant @code{1} or the value from the recursive call @code{loop (i -
1) (i * j)}.  In the latter case, the compiler notices that the
storage for the current argument list is no longer needed, so it may
be reallocated before the recursive call.  This small optimization
means that the tail-recursive version runs in constant space, which
often results in a large performance improvement.

@begin[figure,"imp-fact",t]
@begin[center]
@begin[tabular,ll]
@line{{
@begin[minipage,"2.0in",t]
@begin[verbatim]
let rec fact i =
   if i <= 1 then
      1
   else
      i * fact (i - 1)
@end[verbatim]
@end[minipage]}

{@begin[minipage,"2.0in",t]
@begin[verbatim]
let fact i =
   let rec loop i j =
      if i <= 1 then
         j
      else
         loop (i - 1) (i * j)
   in
      loop i 1
@end[verbatim]
@end[minipage]}}
@end[tabular]
@end[center]
@begin[caption]
Pure functional versions for computing the factorial.  The version on
the left is the simple translation.  The version on the right is a
somewhat more efficient tail-recursive implementation.
@end[caption]
@end[figure]

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
