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
errors, or to control the flow of execution.  When an exception is
raised, the current execution is aborted, and control is thrown to the
most recently entered active exception handler, which may choose to
handle the exception, or pass it through to the next exception
handler.

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
