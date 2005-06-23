doc <:doc< -*- Mode: text; fill-column: 100 -*-

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

As we have seen, functional programming has one central feature---functions are first-class.
Functions may be passed as arguments, returned as the result of function calls, and stored in data
structures just like any other value.  Indeed, the presence of first-class functions is the only
requirement for a programming language to be considered functional.  By this definition, many
programming languages are functional, including not only the usual examples like OCaml, Lisp, and
Haskell, but also languages like Javascript (where functions are associated with fields on a web
page), or even C (where functions are represented with pointers).

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

---JYH: need to add a @bf[difficult] marker ---

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

@section["ref-examples"]{Examples of using reference cells}

@subsection["ref-queue"]{Queues}

A @emph{queue} is a data structure that supports an @emph{enqueue} operation that adds a new value
to the queue, and a @emph{dequeue} operation that removes an element from the queue.  The elements
are dequeued in FIFO (first-in-first-out) order.  Queues are often implemented as imperatide data
structures, where the operations are performed by side-effect.  The following signature gives the
types of the functions to be implemented.

@begin[iverbatim]
    type 'a queue

    val create  : unit -> 'a queue
    val enqueue : 'a queue -> 'a -> unit
    val dequeue : 'a queue -> 'a
@end[iverbatim]

For efficiency, we would like the queue operations to take constant time.  One simple implementation
is to represent the queue as two lists, an @emph{enqueue} list and a @emph{dequeue} list.  When a
value is enqueued, it is added to the enqueue list.  When an element is dequeued, it is taken from
the dequeue list.  If the dequeue list is empty, the queue is @emph{shifted} by setting the dequeue
list to the reversal of the enqueue list.

@begin[iverbatim]
    (* 'a queue = (enqueue_list, dequeue_list) *)
    type 'a queue = 'a list ref * 'a list ref

    (* Create a new empty queue *)
    let create () =
       (ref [], ref [])

    (* Add to the element to the enqueue list *)
    let enqueue (eq, _) x =
       eq := x :: !eq

    (* Remove an element from the dequeue list *)
    let rec dequeue ((eq, dq) as queue) =
        match !dq with
           x :: rest ->
              dq := rest;
              x
         | [] ->  (* Shift the queue *)
              if !eq = [] then
                 raise Not_found;
              dq := List.rev !eq;
              eq := [];
              dequeue queue
@end[iverbatim]

Note that the @code{dequeue} function is defined recursively.  When the @code{dq} list is empty, the
function raises an error if the @code{eq} list is also empty; otherwise, the lists are shifted and
the operation is retried.  The explicit check for an empty queue prevents infinite recursion.

@subsection["ref-tree"]{Cyclic data structures}

One issue with the previous implementation is that the queue must be shifted whenever the dequeue
list becomes empty, which means that the time to perform a dequeue operation can be unpredictable.
In situations where timing is an issue, another common implementation of queues uses a
@emph{circular linked list}, where each element in the list points to the previous element that was
inserted, and the newest element points to the oldest.  If we have a pointer to the newest element,
then we can implement the queue operations in constant time as follows.

@begin[itemize]
@item{To enqueue an element to the queue, add it beween the newest and the oldest.}
@item{The oldest element is the next one after the first.  To dequeue it, remove it from the queue.}
@end[itemize]

This implementation seems straightforward enough, we simply need to construct a circular linked
list.  But this is a problem.  In a pure functional language, cyclic data structures of this form
are not implementable.  When a data value is constructed, it can only be constructed from values
that already exist, not itself.

Once again, reference cells provide a simple way to get around the problem by allowing links in the
list to be set after the elements have already been created.

To begin, we first need to choose a representation for the queue.  First, the elements in the
circular list are of type @code{elem}, which is a pair @code{(x, next)}, where @code{x} is the value
of the element, and @code{next} is the pointer to the next element of the queue.  The queue itself
can be empty, so we define the type as a reference to an @code{elem option}.

@begin[iverbatim]
   (* An element is a pair (value, previous-element) *)
   type 'a elem = 'a * 'a pointer
   and 'a pointer = Pointer of 'a elem ref

   type 'a queue = 'a elem option ref

   let create () =
      None
@end[iverbatim]

You might wonder why not give the @code{'a elem} type a more straightforward definition as @code{'a
* 'a elem ref}.  The problem with this type definition is that it is @emph{cyclic} (since the type
@code{'a elem} appears in its own definition).  By default, OCaml rejects cyclic definitions because
they can be confusing.

@begin[iverbatim]
   % ocaml
        Objective Caml version 3.08.3

   # type 'a elem = 'a * 'a elem ref;;
   The type abbreviation elem is cyclic
@end[iverbatim]

The solution is to introduce a union type (@code{pointer} in this case).  This introduces the
@code{Pointer} constructor, which makes the definition acceptable because the recursive occurence of
@code{elem} in @code{Pointer of 'a elem ref} is now within a constructor.

Next, let's consider the function to add an element to the queue.  The invariant of the queue data
structure is that the each element in the circular list points to the next newer element, and the
newest points to the oldest.  The one exception is when the queue is empty, since there are no
elements.  In this case, when adding the element, we need to create it so that it refers to itself,
since it is simultaneously the oldest and newest element.  This is done with a recursive value
definition, @code{let rec elem = (x, Pointer (ref elem))}, where the element @code{elem} is
defined to point to itself.

@begin[iverbatim]
   let enqueue queue x =
      match !queue with
        None ->
            (* The element should point to itself *)
            let rec elem = (x, Pointer (ref elem)) in
                queue := Some elem
       | Some (_, Pointer prev_next) ->
            (* Insert after the previous element *)
            let oldest = !prev_next in
            let elem = (x, Pointer (ref oldest)) in
               prev_next := elem;
               queue := Some elem
@end[iverbatim]

For the second case, where the queue is non-empty, we create a new element @code{elem} that
points to the oldest element, modify the previous element so that it points to the new element (by
setting the @code{prev_next} reference), and set the queue to point to the new element.

To finish off the implementation, we need to add a function to dequeue an element from the queue.
According to the queue invariant, the oldest element is the element after the newest.  To dequeue
it, we simply unlink it from the queue, with one exception.  If the queue contains only one element,
then that element will point to itself.  We can test for this using the operator @code{==} for
pointer equality; and if so, set the queue to @code{None} to indicate that it is empty.

@begin[iverbatim]
   let dequeue queue =
      match !queue with
         None ->
            (* The queue is empty *)
            raise Not_found
       | Some (_, Pointer oldest_ref) ->
            let oldest = !oldest_ref in
            let (x, Pointer next_ref) = oldest in
            let next = !next_ref in
               (* Test whether the element points to itself *)
               if next == oldest then
                  (* It does, so the queue becomes empty *)
                  queue := None
               else
                  (* It doesn't, unlink it *)
                  oldest_ref := next;
               x
@end[iverbatim]

There are a few things to learn from this example.  For one, it is much more complicated than the
first implementation using two lists.  The type definitions and the data structure itself are
cyclic, and so the implementation is less natural.  For another, we had to make use of two new
operations, the comparison @code{==} for pointer equality, and a @code{let rec} for a recursive
value definition.  In the end, the data structure is more difficult to understand than the two-list
version, and is less likely to be encountered in practice.

@subsection["ref-functional"]{Functional queues with reference cells}

The previous two examples of queues are imperative, meaning that the @code{enqueue} and
@code{dequeue} functions modify the queue in-place.  One might also wonder if there are efficient
functional implementations---that is, rather than modifying the queue in place, the @code{enqueue}
and @code{dequeue} operations produce new queues without effecting the old one.  There are many
advantages to functional data structures.  Among the most important is that functional data
structures are @emph{persistent}---their operations produce new data without destroying old.

It is easy enough to construct a functional version for queues.  Since the operations now return new queues, the signature changes
to the following.

@begin[iverbatim]
    type 'a queue

    val empty   : 'a queue
    val enqueue : 'a queue -> 'a -> 'a queue
    val dequeue : 'a queue -> 'a * 'a queue
@end[iverbatim]

Note that there is no longer a need for a @code{create} function to create a new queue, we can
simply use a canonical empty queue.

For the implementation, let's return to the simpler implementation using two lists.  The first step
is to eliminate all reference cells.  The following code provides this translation.  Note that the
@code{enqueue} operation returns a new queue, and the @code{dequeue} operation returns a pair of an
element and a new queue.

@begin[iverbatim]
    (* The queue is (enqueue_list, dequeue_list) *)
    type 'a queue = 'a list * 'a list

    (* Construct an empty queue *)
    let create () =
       ([], [])

    (* Add the new element to the enqueue_list *)
    let enqueue (eq, dq) x =
       (x :: eq, dq)

    (* Take an element from the dequeue list *)
    let rec dequeue = function
       (eq, x :: dq) ->
          x, (eq, dq)
     | ([], []) ->
          raise Not_found
     | (eq, []) ->
          (* Shift the queue, and dequeue again *)
          dequeue ([], List.rev eq)
@end[iverbatim]

This seems simple enough, and indeed the code is simpler and smaller than the original imperative
version.  Unfortunately, the @code{dequeue} function no longer takes constant time!  Imagine a
scenario where a large number of elements are added to a queue without any intervening dequeue
operations.  The result will be a queue that is maximally imbalanced, with all the elements in the
enqueue list.  If we wish to use the queue multiple times, each time we use the dequeue function,
the queue will have to be shifted by reversing the enqueue list, taking time linear in the number of
elements.

The solution around this uses reference cells to ``remember'' the results of the shift operation.
After all, the shift doesn't change the elements in the queue, it just changes their representation.
Externally, we can preserve the functional appearance of the queue data structure; the
implementation will still be a queue, and it will still be persistent.  The modification that is
needed is to add a reference cell that can be used to shift the queue in-place.

@begin[iverbatim]
    (* The queue is (enqueue_list, dequeue_list) *)
    type 'a queue = ('a list * 'a list) ref

    (* The empty queue is a value *)
    let create () =
       ref ([], [])

    (* Add the new element to the enqueue_list *)
    let enqueue queue x =
       let (eq, dq) = !queue in
          ref (x :: eq, dq)

    (* Take an element from the dequeue list *)
    let rec dequeue queue =
       match !queue with
          (eq, x :: dq) ->
             x, ref (eq, dq)
        | ([], []) ->
             raise Not_found
        | (eq, []) ->
             (* Shift the queue in-place *)
	     queue := ([], List.rev eq);
             dequeue queue
@end[iverbatim]

In this revised version, reference cells are used purely as an optimization.  To preserve the
behavior of the original functional version, when a new queue is created, it is created with a new
reference cell.  This prevents operations on one queue from affecting any others; the data remains persistent.

@subsection["ref-summary"]{Summary}

@subsection["ref-exercises"]{Exercises}

JYH: these are just thoughts for now.

@begin[enumerate]
@item{{In the implementation of queues as circular lists, we used a recursive value definition.

@begin[iverbatim]
   let rec elem = (x, Pointer (ref elem)) in ...
@end[iverbatim]

Many languages do not have this feature.  What would you need to do if values could not be defined recursively?
What would be the impact on performance?}}

@item{{While the comparison @code{==} is frequently understood as physical (pointer) equality, the
OCaml documentation gives a weaker definition, ``For any two values @code{x} and @code{y}, if
@code{x == y} then @code{x = y}.''  According to this definition, it would be acceptable if the
@code{==} comparison always returns @code{false}.  What would happen to the implementation of queues
using circular linked lists if so?  How could it be fixed?}}

@item{{The functional versions of the queue have a @code{create} function that returns a fresh, empty queue.
Since the data structure is functional, it would be reasonable to replace the @code{create} function with a value
@code{code} empty that represents the empty queue.  For example, in the purely function version, we could define
the empty queue as the following, and remove the @code{create} function.

@begin[iverbatim]
    let empty = ([], [])
@end[iverbatim]

Why won't this work in the version of the queue that uses reference cells?}}

@item{{Is it possible to implement a persistent queue using circular linked lists, and all
operations are $O(1)$ (constant time)?  If so, provide an implementation.  If not, explain why
not.}}

@end[enumerate]

@end[doc]
@docoff
>>

(*
 * -*-
 * Local Variables:
 * fill-column: 100
 * Caml-master: "compile"
 * End:
 * -*-
 *)
