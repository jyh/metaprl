doc <:doc< -*- Mode: text -*-

   @begin[doc]
   @chapter[exceptions]{Exceptions}
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
first element in a list.  If the list is empty, we would like to
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
striking at first---it appears to say that the raise function can
produce a value having @emph{any} type.  In fact, what it really means
is that the @code{raise} function never returns, and so the type of
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
stack order.  If the topmost handler contains a apttern that matches
the raised exception, it receives control.  Otherwise, the handler is
popped from the stack, and the next handler is examined.

In our example, when the @code{split} function raises the @code{Empty}
exception, the top four elements of the exception stack contain
handlers corresponding to each of the recursive calls of the
@code{map} function.  When the @code{Empty} exception is raised,
control is passed to the innermost call @code{map f []}, which returns
the empty list as a result.

@begin[tabular,"|c|"]
@hline
@line{@code{map f []}}
@line{@code{map f [7]}}
@line{@code{map f [5; 7]}}
@line{@code{map f [3; 5; 7]}}
@hline
@end[tabular]

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
in magnificent ways.  In this section we cover some standard uses of
exceptions, and some of the abuses.

@section["old-exceptions"]{Old text}

Unlike a @code{match} expression, the cases in a @emph{try} expression do not have to exhaustive.  If an exception does not match one of the cases,



Exceptions were designed as a more elegant alternative to explicit
error handling in more traditional languages.  In Unix/C, for example,
most system calls return @code{-1} on failure, and @code{0} on
success.  System code tends to be cluttered with explicit error
handling code that obscures the intended operation of the code.  In the
OCaml @tt{Unix} module, the system call stubs raise an exception on
failure, allowing the use of a single error handler for a block of
code.  In some ways, this is like the @tt{setjmp/longjmp} interface in
C, but OCaml exceptions are safe.

To see how this works, consider the @code{List.assoc} function, which
is defined as follows.

@begin[iverbatim]
# let rec assoc key = function
     (k, v) :: l ->
        if k = key then
           v
        else
           assoc key l
   | [] ->
        raise Not_found;;
val assoc : 'a -> ('a * 'b) list -> 'b = <fun>
# let l = [1, "Hello"; 2, "World"];;
val l : (int * string) list = [1, "Hello"; 2, "World"]
# assoc 2 l;;
- : string = "World"
# assoc 3 l;;
Uncaught exception: Not_found
# "Hello" ^ assoc 2 l;;
- : string = "HelloWorld"
# "Hello" ^ assoc 3 l;;
Uncaught exception: Not_found
@end[iverbatim]

In the first case, @code{assoc 2 l}, the key is found in the list and
its value is returned.  In the second case, @code{assoc 3 l}, the key
@code{3} does not exist in the list, and the exception
@code{Not_found} is raised.  There is no explicit exception handler,
and the toploop default handler is invoked.

Exceptions are declared with the @code{exception} keyword, and their
syntax has the same form as a constructor declaration in a union type.
Exceptions are raised with the @code{raise} function.

@begin[iverbatim]
# exception Abort of int * string;;
exception Abort of int * string
# raise (Abort (1, "GNU is not Unix"));;
Uncaught exception: Abort(1, "GNU is not Unix")
@end[iverbatim]

Exception handlers have the same form as a @tt{match} pattern match,
using the @tt{try} keyword.  The syntax is as follows:

@begin[center]
@begin[tabular, l]
@line{{@tt{try}$@space$ e$@space$ @tt{with}}}
@line{{@phantom{$@space$ |} p_1 $@space$ @tt{->} $@space$ e_1}}
@line{{$@space$ | p_2 $@space$ @tt{->} $@space$ e_2}}
@line{{@phantom{$@space$ |} $@vdots$}}
@line{{$@space$ | p_n $@space$ @tt{->} $@space$ e_n}}
@end[tabular]
@end[center]

First, $e$ is evaluated.  If it does not raise an exception, its value
is returned as the result of the @tt{try} statement.  Otherwise, if
an exception is raised during evaluation of $e$, the exception is
matched against the patterns $p_1, @ldots, p_n$.  If the first pattern
the exception matches is $p_i$, the expression $e_i$ is evaluated and returned
as the result.  Otherwise, if no pattern matches, the exception is
propagated to the next exception handler.

@begin[iverbatim]
# try "Hello" ^ assoc 2 l with
     Abort (i, s) -> s
   | Not_found -> "Not_found";;
- : string = "HelloWorld"
# try "Hello" ^ assoc 3 l with
     Abort (i, s) -> s
   | Not_found -> "Not_found";;
- : string = "Not_found"
# try "Hello" ^ assoc 3 l with
     Abort (i, s) -> s;;
Uncaught exception: Not_found
@end[iverbatim]

Exceptions are also used to manage control flow.  For example,
consider the binary trees in the previous chapter.

@begin[iverbatim]
# type 'a btree =
     Node of 'a btree * 'a * 'a btree
   | Leaf;;
type 'a btree = | Node of 'a btree * 'a * 'a btree | Leaf
@end[iverbatim]

Suppose we wish to build a @tt{replace} function that replaces a value
in the set.  The expression @code{replace x y s} should replace value
@tt[x] with @tt[y] in tree @tt[s], or raise the exception
@code{Not_found} if the value does not exist.

@begin[iverbatim]
# let rec replace x y = function
     Leaf -> raise Not_found
   | Node (left, z, right) ->
        let left, mod_left =
           try replace x y left, true with
              Not_found -> left, false
        in
        let right, mod_right =
           try replace x y right, true with
              Not_found -> right, false
        in
           if z = x then
              Node (left, y, right)
           else if mod_left || mod_right then
              Node (left, x, right)
           else
              raise Not_found;;
val replace : 'a -> 'a -> 'a btree -> 'a btree = <fun>
@end[iverbatim]

In this function, the left and right subtrees are recursively
modified.  The @tt{mod_left} and @tt{mod_right} flags are set iff the
corresponding branches were modified.  If neither branch is modified,
the @code{Not_found} exception is raised.

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
