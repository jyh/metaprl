(* -*- Mode: text -*- *)
doc <:doc<
   @begin[doc]
   @spelling{doesn ii wildcard}

   @chapter[exceptions]{Exceptions}

   @docoff
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
   @end[doc]
>>

extends Base_theory

doc <:doc<
@begin[doc]

Exceptions are used in OCaml as a control mechanism, either to signal
errors, or control the flow of execution in some other way.  In their
simplest form, exceptions are used to signal that the current
computation cannot proceed because of a run-time error.  For example,
if we try to evaluate the quotient @code{1 / 0} in the toploop, the
runtime signals a @code{Division_by_zero} error, the computation is
aborted, and the toploop prints an error message.

@begin[iverbatim]
# 1 / 0;;
Exception: Division_by_zero.
@end[iverbatim]

Exceptions can also be defined and used explicitly by the programmer.
For example, suppose we define a function @code{head} that returns the
first element of a list.  If the list is empty, we would like to
signal an error.

@begin[iverbatim]
# exception Fail of string;;
exception Fail of string
# let head = function
     h :: _ -> h
   | [] -> raise (Fail "head: the list is empty");;
val head : 'a list -> 'a = <fun>
# head [3; 5; 7];;
- : int = 3
# head [];;
Exception: Fail "head: the list is empty".
@end[iverbatim]

The first line of this program defines a new exception, declaring
@code{Fail} as a new exception with a string argument.  The
@code{head} function computes by pattern matching---the result is
@code{h} if the list has first element @code{h}; otherwise, there is
no first element, and the @code{head} function raises a @code{Fail}
exception.  The expression @code{(Fail "head: the list is empty")} is
a value of type @code{exn}; the @code{raise} function is responsible
for aborting the current computation.

@begin[iverbatim]
# Fail "message";;
- : exn = Fail "message"
# raise;;
- : exn -> 'a = <fun>
# raise (Fail "message");;
Exception: Fail "message".
@end[iverbatim]

The type @code{exn -> 'a} for the @code{raise} function may seem
surprising at first---it appears to say that the raise function can
produce a value having @emph{any} type.  In fact, what it really means
is that the @code{raise} function never returns, so the type of
the result doesn't matter.  When a @code{raise} expression occurs in a
larger computation, the entire computation is aborted.

@begin[iverbatim]
# 1 + raise (Fail "abort") * 21;;
Exception: Fail "abort".
@end[iverbatim]

When an exception is raised, the current computation is aborted, and
control is passed directly to the currently active exception handler,
which in this case is the toploop itself.  It is also possible to
define explicit exception handlers.  For example, suppose we wish to
define a function @code{head_default}, similar to @code{head}, but
returning a default value if the list is empty.  One way would be to
write a new function from scratch, but we can also choose to handle
the exception from @code{head}.

@begin[iverbatim]
# let head_default l default =
     try head l with
        Fail _ -> default;;
val head_default : 'a list -> 'a -> 'a = <fun>
# head_default [3; 5; 7] 0;;
- : int = 3
# head_default [] 0;;
- : int = 0
@end[iverbatim]

The @code{try} $e$ @code{with} @emph{cases} expression is very much
like a @code{match} expression, but it matches exceptions that are
raised during evaluation of the expression $e$.  If $e$ evaluates to a
value without raising an exception, the value is returned as the
result of the @code{try} expression.  Otherwise, the raised exception
is matched against the patterns in @emph{cases}, and the first
matching case is selected.  In the example, if evaluation of
@code{head l} raises the @code{Fail} exception, the value
@code{default} is returned.

@section["nested-exceptions"]{Nested exception handlers}

Exceptions are handled dynamically, and at run-time there may be many
active exception handlers.  To illustrate this, let's consider an
alternate form of a list-map function, defined using a function
@code{split} that splits a non-empty list into its head and tail.

@begin[iverbatim]
# exception Empty;;
exception Empty
# let split = function
     h :: t -> h, t
   | [] -> raise Empty;;
val split : 'a list -> 'a * 'a list = <fun>
# let rec map f l =
     try
        let h, t = split l in
           f h :: map f t
     with
        Empty -> [];;
val map : ('a -> 'b) -> 'a list -> 'b list = <fun>
# map (fun i -> i + 1) [3; 5; 7];;
- : int list = [4; 6; 8]
@end[iverbatim]

The call to @code{map} on the three-element list @code{[3; 5; 7]}
results in four recursive calls corresponding to @code{map f [3; 5;
7]}, @code{map f [5; 7]}, @code{map f [7]}, and @code{map f []},
before the function @code{split} is called on the empty list.  Each of
the calls defines a new exception handler.

It is appropriate to think of these handlers forming an exception
stack corresponding to the call stack (this is, in fact, they way it
is implemented in the OCaml implementation from INRIA).  When a
@code{try} expression is evaluated, a new exception handler is pushed
onto the the stack; the handler is removed when evaluation completes.
When an exception is raised, the entries of the stack are examined in
stack order.  If the topmost handler contains a pattern that matches
the raised exception, it receives control.  Otherwise, the handler is
popped from the stack, and the next handler is examined.

In our example, when the @code{split} function raises the @code{Empty}
exception, the top four elements of the exception stack contain
handlers corresponding to each of the recursive calls of the
@code{map} function.  When the @code{Empty} exception is raised,
control is passed to the innermost call @code{map f []}, which returns
the empty list as a result.

@begin[center]
@begin[tabular,"|l|"]
@hline
@line{@code{map f []}}
@hline
@line{@code{map f [7]}}
@hline
@line{@code{map f [5; 7]}}
@hline
@line{@code{map f [3; 5; 7]}}
@hline
@end[tabular]
@end[center]

This example also contains a something of a surprise.  Suppose the
function @code{f} raises the @code{Empty} exception?  The program
gives no special status to @code{f}, and control is passed to the
uppermost handler on the exception stack.  As a result, the list is
truncated at the point where the exception occurs.

@begin[iverbatim]
# map (fun i ->
          if i = 0 then
             raise Empty
          else
             i + 1) [3; 5; 0; 7; 0; 9];;
- : int list = [4; 6]
@end[iverbatim]

@section["exception-examples"]{Examples of uses of exceptions}

Like many other powerful language constructs, exceptions can used to
simplify programs and improve their clarity.  They can also be abused
in many ways.  In this section we cover some standard uses of
exceptions, and some of the abuses.

@subsection["exception-match"]{Pattern matching failure}

The OCaml standard library uses exceptions for many purposes.  We have
already seen how exceptions are used to handle some run-time errors
like incomplete pattern matches.  When a pattern matching is
incompletely specified, the OCaml compiler issues a warning (and a
suggestion for the missing pattern).  At runtime, if the matching
fails because it is incomplete, the @code{Match_failure} exception is
raised.  The three values are the name of the file, the line number,
and the character offset within the line where the match failed.  It
is often considered bad practice to catch the @code{Match_failure}
exception because the failure usually indicates a programming error
(in fact, proper programming practice would dictate that all pattern
matches be complete).

@begin[iverbatim]
# let f x =
     match x with
        Some y -> y;;
Warning: this pattern-matching is not exhaustive.
Here is an example of a value that is not matched:
None
val f : 'a option -> 'a = <fun>
# f None;;
Exception: Match_failure ("", 2, 3).
@end[iverbatim]

@subsection["exception-assert"]{Assertions}

Another common use of exceptions is for checking runtime invariants.
The @code{assert} operator evaluates a Boolean expression, raising an
@code{Assert_failure} exception if the value is @code{false}.  For
example, in the following version of the factorial function, an
assertion is used to generate a runtime error if the function is not
called with a negative argument.  The three arguments represent the
file, line, and character offset of the failed assertion.  As with
@code{Match_failure}, it is considered bad programming practice to
catch the @code{Assert_failure} exception.

@begin[iverbatim]
# let rec fact i =
     assert (i >= 0);
     if i = 0 then
        1
     else
        i * fact (i - 1);;
val fact : int -> int = <fun>
# fact 10;;
- : int = 3628800
# fact (-10);;
Exception: Assert_failure ("", 9, 3).
@end[iverbatim]

@subsection["exception-failure"]{Invalid_argument and Failure}

The @code{Invalid_argument} exception is similar to an assertion
failure; it indicates that some kind of runtime error occurred.  One
of the more common causes is array and string subscripts that are
out-of-bounds.  The @code{Invalid_argument} exception includes a
string describing the error.

@begin[iverbatim]
# let a = [|5; 6; 7|];;
val a : int array = [|5; 6; 7|]
# a.(2);;
- : int = 7
# a.(3);;
Exception: Invalid_argument "index out of bounds".
@end[verbatim]

The @code{Failure} exception is similar, but it is usually used to
signal errors that are considered less severe.  The @code{Failure}
exception also includes a string describing the error.  The standard
convention is that the string describing the failure should be the
name of the function that failed.

@begin[iverbatim]
# int_of_string "0xa0";;
- : int = 160
# int_of_string "0xag";;
Exception: Failure "int_of_string".
@end[iverbatim]

The @code{Invalid_argument} and @code{Failure} exceptions are quite
similar---they each indicate a run-time error, using a string
to describe it, so what is the difference?

The difference is primarily a matter of style.  The
@code{Invalid_argument} exception is usually used to indicate
@emph{programming} errors, or errors that should never happen if the
program is correct, similar to assertion failures.  The @code{Failure}
exception is used to indicate errors that are more benign, where it is
possible to recover, and where the cause is often due to external
events (for example, when a string @code{0xag} is read in a place
where a number is expected).

For illustration, suppose we are given a pair of lists, @code{names} and
@code{grades}, that describe the students taking a class.  We are told
that every student in the class must have a grade, but not every
student is taking the class.  We might define the function to return a
student's grade by recursively search through the two lists until the
entry for the student is found.

@begin[iverbatim]
let rec find_grade student (names, grades) =
   match (names, grades) with
      (name :: names'), (grade :: grades') ->
         if name = student then
            grade
         else
            find_grade student (names', grades')
    | [], [] ->
         raise (Failure "student not enrolled in the class")
    | [], (_ ::_)
    | (_ :: _), [] ->
         raise (Invalid_argument "corrupted database")
@end[iverbatim]

The first match clause handles the case where the two lists are
nonempty, returning the student's grade if the name matches, and
continuing with the rest of the lists otherwise.  In the second
clause, when both lists are empty, the search fails.  Since this kind
of failure is expected to happen occasionally, the proper exception is
@code{Failure}.  In the final clause, it is found that the
@code{names} and @code{grades} lists have different lengths.  The
proper exception in this case is @code{Invalid_argument} because i)
the error violates a key programming invariant (that every student has
a grade), and ii) there is no obvious way to recover.  As a matter of
style, it is usually considered bad practice to catch
@code{Invalid_argument} exceptions (in fact, some early OCaml
implementations did not even allow it).  In contrast, @code{Failure}
exceptions are routinely caught so that the error can be corrected.

@subsection["exception-notfound"]{The Not_found exception}

The @code{Not_found} exception is used by search functions to indicate
that a search failed.  There are many such functions in OCaml.  One
example is the @code{List.assoc} function, which searches for a
key-value pair in a list.  For instance, instead of representing the
grades in the previous example as two lists, we might represent the
grades as a list of pairs (this will also enforce the requirement that
every student have a grade).

@begin[iverbatim]
# let grades = [("John", "B-"); ("Jane", "A"); ("Joan", "C")];;
val grades : (string * string) list = ...
# List.assoc "Jane" grades;;
- : string = "A"
# List.assoc "June" grades;;
Exception: Not_found.
@end[iverbatim]

Stylistically, the @code{Not_found} exception is often routine, and
expected to happen during normal program operation.

@subsection["exception-failure"]{Memory exhaustion exceptions}

The two exceptions @code{Out_of_memory} and @code{Stack_overflow}
indicate that memory resources have been exhausted.  The
@code{Out_of_memory} exception is raised by the garbage collector when
there is insufficient memory to continue running the program.  The
@code{Stack_overflow} exception is similar, but it is restricted just
to stack space.  The most common cause of a @code{Stack_overflow}
error is deep recursion (for example, using the @code{List.map}
function on a list with more than a few thousand elements), or an
infinite loop in the program.

Both errors are severe, and the exceptions should not be caught
casually.  For the @code{Out_of_memory} exception it is often useless
to catch the exception without freeing some resources, since the
exception handler will usually not be able to execute if all memory
has been exhausted.

Catching the @code{Stack_overflow} exception is not advised for a
different reason.  While the @code{Stack_overflow} exception can be
caught reliably by the byte-code interpreter, it is not supported by
the native-code compiler on all architectures.  In many cases, a stack
overflow will result in a system error (a ``segmentation fault''),
instead of a runtime exception.  For portability, it is often better
to avoid catching the exception.

@section["exception-control"]{Other uses of exceptions}

Exceptions are also frequently used to modify the control flow of a
program, without necessarily being associated with any kind of error
condition.

@subsection["exception-remove"]{Decreasing memory usage}

As a simple example, suppose we wish to write a function to remove the
first occurrence of a particular element ``x'' in a list ``l''.  The
straightforward implementation is defined as a recursive function.

@begin[iverbatim]
let rec remove x = function
   y :: l when x = y ->
      l
 | y :: l (* x <> y *) ->
      y :: remove x l
 | [] ->
      []
@end[iverbatim]

The @code{remove} function searches through the list for the first
occurrence of an element @code{y} that is equal to @code{x},
reconstructing the list after the removal.

One problem with this function is that the entire list is copied
needlessly when the element is not found, potentially increasing the
space needed to run the program.  Exceptions provide a convenient way
around this problem.  By raising an exception in the case where the
element is not found, we can avoid reconstructing the entire list.  In
the following function, when the @code{Unchanged} exception is raised,
the @code{remove} function returns the original list @code{l}.

@begin[iverbatim]
exception Unchanged

let rec remove_inner x = function
   y :: l when x = y ->
      l
 | y :: l (* x <> y *) ->
      y :: remove_inner x l
 | [] ->
      raise Unchanged

let remove x l =
   try remove_inner x l with
      Unchanged ->
         l
@end[verbatim]

@subsection["exception-break"]{Break statements}

While OCaml provides both ``@code{for}'' and ``@code{while}'' loops,
there is no ``@code{break}'' statement as found in languages like C
and Java.  Instead, exceptions can be used to abort a loop execution.
To illustrate this, suppose we want to define a function @code{cat}
that prints out all the lines from the standard input channel.  We
discuss input/output in more detail in Section @refsection[io], but
for this problem we can just use the standard functions
@code{input_char} to read a character from the input channel, and
@code{output_char} to write it to the output channel.  The
@code{input_char} function raises the exception @code{End_of_file}
when the end of the input has been reached.

@begin[iverbatim]
let cat in_channel out_channel =
   try
      while true do
         output_char out_channel (input_char in_channel)
      done
   with
      End_of_file ->
         ()
@end[iverbatim]

The @code{cat} function defined an infinite loop (@code{while true do
... done}) to copy the input data to the output channel.  When the end
of the input has been reached, the @code{input_char} function raises
the @code{End_of_file} exception, breaking out of the loop, returning
the @code{()} value as the result of the function.

@subsection["exception-unwind"]{Unwind-protect (finally)}

In some cases where state is used, it is useful to define a
``finally'' clause (similar to an ``unwind-protect'' as seen in Lisp
languages).  The purpose of a ``finally'' clause is to execute some
code (usually to clean up) after an expression is evaluated.  In
addition, the finally clause should be executed even if an exception
is raised.  A generic @code{finally} function can be defined using a
wildcard exception handler.  In the following function, the
@code{result} type is used to represent the result of executing the
function ``f'' on argument ``x,'' returning a @code{Success} value if
the evaluation was successful, and @code{Failure} otherwise.  Once the
result is computed, the @code{cleanup} function is called, and i) the
result is returned on @code{Success}, or ii) the exception is
re-raised on @code{Failure}.

@begin[iverbatim]
type 'a result =
   Success of 'a
 | Failure of exn

let finally f x cleanup =
   let result =
      try Success (f x) with
         exn ->
            Failure exn
   in
      cleanup ();
      match result with
         Success y -> y
       | Failure exn -> raise exn
@end[iverbatim]

For example, suppose we wish to process in input file.  The file
should be opened, processed, and it should be closed afterward
(whether or not the processing was successful).  We can implement this
as follows.

@begin[iverbatim]
let process in_channel =
   ...

let process_file file_name =
   let in_channel = open_in file_name in
      finally process in_channel (fun () -> close_in in_channel)
@end[iverbatim]

In this example the @code{finally} function is used to ensure that the
@code{in_channel} is closed after the input file is processed, whether
or not the @code{process} function was successful.

@subsection["exception-type"]{The @tt[exn] type}

We close with a somewhat unorthodox use of exceptions completely
unrelated to control flow.  Exceptions (values of the @code{exn} type)
are first-class values; they can be passed as arguments, stored in
data structures, etc.  The values in the @code{exn} type are specified
with @code{exception} definitions.  One unique property of the
@code{exn} type is that it is @emph{open} so that new exceptions can
be declared when desired.  This mechanism can be used to provide a
kind of dynamic typing, much like the open unions discussed in Section
@refsection["open-unions"].

For example, suppose we want to define a list of values, where the
type of the values can be extended.  Initially, we might want lists
containing strings and integers, and suppose we wish to define a
@code{succ} function that increments every integer in the list.

@begin[iverbatim]
# exception String of string;;
# exception Int of int;;
# let succ l =
     List.map (fun x ->
        match x with
           Int i -> Int (i + 1)
         | _ -> x) l;;
val succ : exn list -> exn list = <fun>
# let l = succ [String "hello"; Int 1; Int 7];;
val l : exn list = [String "hello"; Int 2; Int 8]
@end[iverbatim]

Later, we might also decide to add floating-point numbers to the list,
with their own successor function.

@begin[iverbatim]
# exception Float of float;;
exception Float of float
# let succ_float l =
     List.map (fun x ->
        match x with
           Float y -> Float (y +. 1.0)
         | _ -> x) l;;
val succ_float : exn list -> exn list = <fun>
# succ_float (Float 2.3 :: l);;
- : exn list = [Float 3.3; String "hello"; Int 2; Int 8]
@end[verbatim]

The main purpose of this example is to illustrate properties of
exception values.  In cases where extendable unions are needed, the
use of open union types is more appropriate.  Needless to say, it can
be quite confusing to encounter data structures constructed from
exceptions!

@end[doc]
>>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
