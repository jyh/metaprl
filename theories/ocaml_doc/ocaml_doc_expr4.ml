(*!
 * @begin[spelling]
 * Dereferencing blit bool doesn downto fields int
 * jason ll namespace permissable rec ref toplevel
 * @end[spelling]
 *
 * @begin[doc]
 * @chapter[records]{Records, Arrays, Exceptions, and Side-Effects}
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

In this chapter we discuss the remaining data types, all of which
allow side-effects.  The record type can be viewed as the type of
tuples where the components are labeled.  An array is a fixed-size
vector of items with constant time access to each element.  There are
operations to modify some of the fields in a record, and any of the
fields in an array.

@section[records]{Records}

A record is a labeled collection of values of arbitrary types.  The
syntax for a record type is a set of field type definitions surrounded
by braces, and separated by semicolons.  Field types are declared as
@code{label : type}, where the label is an identifier that must begin
with a lowercase letter or an underscore.  For example, the following
record is redefines the database entry from Chapter
@refchapter[tuples].

@begin[verbatim]
# type db_entry =
     { name : string;
       height : float;
       phone : string;
       salary : float
     };;
type db_entry = { name: string; height: float; phone: string; salary: float }
@end[verbatim]

The syntax for a value is similar to the type declaration, but the
fields are defined as @code{label = expr}.  Here is an example
database entry.

@begin[verbatim]
# let jason =
     { name = "Jason";
       height = 6.25;
       phone = "626-395-6568";
       salary = 50.0
     };;
val jason : db_entry =
  {name="Jason"; height=6.25; phone="626-395-6568"; salary=50}
@end[verbatim]

There are two ways to get access to the fields in a record.  The
projection operation @code{r.l} returns the field labeled @tt{l} in
record @tt{r}.

@begin[verbatim]
# jason.height;;
- : float = 6.25
# jason.phone;;
- : string = "626-395-6568"
@end[verbatim]

Pattern matching can also be used to access the fields of a record.
The syntax for a pattern is like a record value, but the fields
contain a label and a pattern @code{label = patt}.

@begin[verbatim]
# let { name = n; height = h } = jason;;
val n : string = "Jason"
val h : float = 6.25
@end[verbatim]

There are two update operations: a functional version, and an
imperative version.  The functional version produces a copy of a
record with new values for the specified fields.  The syntax for a
functional update uses the @tt{with} keyword in a record definition.

@begin[verbatim]
# let dave = { jason with name = "Dave"; height = 5.9 };;
val dave : db_entry =
  {name="Dave"; height=5.9; phone="626-395-6568"; salary=50}
# jason;;
- : db_entry = {name="Jason"; height=6.25;
                phone="626-395-6568"; salary=50}
@end[verbatim]

@subsection[record_update]{Record updates}

Record fields can also be modified by assignment, but @emph{only if
the record field is declared as @bf{mutable}}.  The syntax for a
mutable field uses the @tt{mutable} keyword before the field label.
For example, if we wanted to allow salaries to be modified, we would
redeclare the record entry as follows.

@begin[verbatim]
# type db_entry =
     { name : string;
       height : float;
       phone : string;
       mutable salary : float
     };;
type db_entry =
  { name: string;
    height: float;
    phone: string;
    mutable salary: float }
# let jason =
    { name = "Jason";
      height = 6.25;
      phone = "626-395-6568";
      salary = 50.0
    };;
val jason : db_entry =
  {name="Jason"; height=6.25; phone="626-395-6568"; salary=50}
@end[verbatim]

The syntax for a field update is @code{r.label <- expr}.  For example,
if we want to give @tt{jason} a raise, we would use the following statement.

@begin[verbatim]
# jason.salary <- 150.0;;
- : unit = ()
# jason;;
- : db_entry = {name="Jason"; height=6.25; phone="626-395-6568"; salary=150}
@end[verbatim]

Note that the assignment statement itself returns the canonical unit
value @code{()}.  That is, it doesn't really return a value, unlike
the functional update.  A functional update creates a completely new
copy of a record; assignments to the copies will be independent.

@begin[verbatim]
# let dave = { jason with name = "Dave" };;
val dave : db_entry =
  {name="Dave"; height=6.25; phone="626=395-6568"; salary=150}
# dave.salary <- 180.0;;
- : unit = ()
# dave;;
- : db_entry = {name="Dave"; height=6.25; phone="626=395-6568"; salary=180}
# jason;;
- : db_entry = {name="Jason"; height=6.25; phone="626=395-6568"; salary=150}
@end[verbatim]

@subsection[record_labels]{Field label namespace}

One important point: the namespace for record field labels is flat.
That is, all labels are defined at the toplevel in the same
namespace.  This is important if you intend to declare records with
the same field names.  If you do, the original labels will be lost!
For example, consider the following sequence.

@begin[verbatim]
# type rec1 = { name : string; height : float };;
type rec1 = { name: string; height: float }

# let jason = { name = "Jason"; height = 6.25 };;
val jason : rec1 = {name="Jason"; height=6.25}

# type rec2 = { name : string; phone : string };;
type rec2 = { name: string; phone: string }

# let dave = { name = "Dave"; phone = "626-395-6568" };;
val dave : rec2 = {name="Dave"; phone="626-395-6568"}

# jason.name;;
Characters 0-5:
This expression has type rec1 but is here used with type rec2

# dave.name;;
- : string = "Dave"

# let bob = { name = "Bob"; height = 5.75 };;
Characters 10-41:
The label height belongs to the type rec1
but is here mixed with labels of type rec2
@end[verbatim]

In this case, the @tt{name} field was redefined.  At this point, the
original @code{rec1.name} label is lost, making it impossible to
access the name field in a value of type @tt{rec1}, and impossible to
construct new values of type @tt{rec1}.  It is, however, permissable
to use the same label names in separate files, as we will see in
Chapter @refchapter[modules].

@section[references]{References}

Mutable variables are common enough in OCaml programs that a special
form is defined just for this case.  Mutable fields use the @tt{ref}
function.

@begin[verbatim]
# let i = ref 1;;
val i : int ref = {contents=1}
@end[verbatim]

The built-in type @code{'a ref} is defined using a regular record
definition; the normal operations can be used on this record.

@begin[verbatim]
type 'a ref = { mutable contents : 'a }
@end[verbatim]

Dereferencing uses the @code{!} operator, and assignment uses the
@code{:=} infix operator.

@begin[verbatim]
# i := 17;;
- : unit = ()
# !i;;
- : int = 17
@end[verbatim]

Don't get confused with the @code{!} operator in C here.  the
following code can be confusing.

@begin[verbatim]
# let flag = ref true;;
val flag : bool ref = {contents=true}
# if !flag then 1 else 2;;
- : int = 1
@end[verbatim]

You may be tempted to read @code{if !flag then ...} as testing if the
@tt{flag} is false.  This is @emph{not} the case; the @code{!}
operator is more like the @code{*} operator in C.

@subsection[ref_value_restriction]{Value restriction}

As we mentioned in Section @refsection[value_restriction], side-effect
interact with type inference.  We considered, for example, an
``identity'' function that saves a value on its first call, and
returns that value on all future calls.  This function is not properly
polymorphic.  We can illustrate this using a single variable.

@begin[verbatim]
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
# one_shot 2;;
- : int = 1
# one_shot "Hello";;
Characters 9-16:
This expression has type string but is here used with type int
@end[verbatim]

The value restriction requires that polymorphism be restricted to
values.  Values include constants, and constructors with fields that
are values, and non-mutable records with fields that are values.
An application is @emph{not} a value, and a record with mutable fields
is not a value.  By this definition, the @tt{x} and @tt{one_shot}
variables cannot be polymorphic, as the type constants @code{'_a}
indicate.

@section[arrays]{Arrays and strings}

Arrays are fixed-size vectors of values.  All of the values must have
the same type.  The fields in the array may be accessed and modified
in constant time.  Arrays can be created with the $@tt{[|} e_1; @ldots; e_n
@tt{|]}$ syntax, which creates an array of length $n$ initialized with
the values computed from the expressions $e_1, @ldots, e_n$.

@begin[verbatim]
# let a = [|1; 3; 5; 7|];;
val a : int array = [|1; 3; 5; 7|]
@end[verbatim]

Fields can be accessed with the $a@tt{.(}i@tt{)}$ construction.  Array
indices start from 0; array bounds are checked.

@begin[verbatim]
# a.(0);;
- : int = 1
# a.(1);;
- : int = 3
# a.(5);;
Uncaught exception: Invalid_argument("Array.get")
@end[verbatim]

Fields are updated with the $a@tt{.(}i@tt{) <-} e$ assignment
statement.

@begin[verbatim]
# a.(2) <- 9;;
- : unit = ()
# a;;
- : int array = [|1; 3; 9; 7|]
@end[verbatim]

The @tt{Array} library module defines additional functions on arrays.
Arrays of arbitrary length can be created with the @code{Array.create}
function, which requires a length and initializer argument.  The
@code{Array.length} function returns the number of elements in the
array.

@begin[verbatim]
# let a = Array.create 10 1;;
val a : int array = [|1; 1; 1; 1; 1; 1; 1; 1; 1; 1|]
# Array.length a;;
- : int = 10
@end[verbatim]

The @code{Array.blit} function can be used to copy elements from one
array to another.  The @tt{blit} function requires five arguments: the
source array, a starting offset into the array, the destination array, a
starting offset into the destination array, and the number of elements
to copy.

@begin[verbatim]
# Array.blit [| 3; 4; 5; 6 |] 1 a 3 2;;
- : unit = ()
# a;;
- : int array = [|1; 1; 1; 4; 5; 1; 1; 1; 1; 1|]
@end[verbatim]

In OCaml, strings are a lot like packed arrays of characters.  The
access and update operations use the syntax $s@tt{.[}i@tt{]}$ and
$s@tt{.[}i@tt{] <-} c$ operators.

@begin[verbatim]
# let s = "Jason";;
val s : string = "Jason"
# s.[2];;
- : char = 's'
# s.[3] <- 'y';;
- : unit = ()
# s;;
- : string = "Jasyn"
@end[verbatim]

The @tt{String} module defines additional functions, including the
@code{String.length} and @code{String.blit} functions that parallel
the corresponding @tt{Array} operations.  The @code{String.create}
function does not require an initializer.  It creates a string with
arbitrary contents.

@begin[verbatim]
# String.create 10;;
- : string = "\000\011\000\000,\200\027@\000\000"
# String.create 10;;
- : string = "\196\181\027@\001\000\000\000\000\000"
@end[verbatim]

@section[looping]{Sequential execution and looping}

Sequential execution is not useful in a functional language--why
compute a value and discard it?  In an imperative language, including
a language like OCaml, sequential execution is needed to compute by
side-effect.

Sequential execution is defined using the semicolon operator.  The
expression $e_1; e_2$ evaluates $e_1$, discards the result (it
probably has a side-effect), and evaluates $e_2$.  Note that the
semicolon is a @emph{separator} (as in Pascal), not a
@emph{terminator} (as in C).  The compiler produces a warning if
expression $e_1$ does not have type @tt{unit}.  As usual, heed these
warnings!  The @code{ignore : 'a -> unit} function can be used if you
really want to discard a non-unit value.

There are two kinds of loops in OCaml, a @tt{for} loop, and a
@tt{while} loop.  The @tt{while} loop is simpler; we'll start there.

@subsection[while_loop]{@tt{while} loops}

The @tt{while} loop has the syntax $@tt{while}@space e_1@space
@tt{do}@space e_2@space @tt{done}$.  The expression $e_1$ must have
type @tt{bool}.  When a @tt{while} loop is evaluated, the expression
$e_1$ is evaluated first.  If it is false, the @tt{while} loop
terminates.  Otherwise, $e_2$ is evaluated, and the loop is evaluated
again.

Here is an example to check if a value @tt{x} is in an array @tt{a}.

@begin[verbatim]
# let array_mem x a =
     let len = Array.length a in
     let flag = ref false in
     let i = ref 0 in
        while !flag = false && !i < len do
           if a.(!i) = x then
              flag := true;
           i := !i + 1
        done;
        !flag;;
val array_mem : 'a -> 'a array -> bool = <fun>
# array_mem 1 [| 3; 5; 1; 6|];;
- : bool = true
# array_mem 7 [| 3; 5; 1; 6|];;
- : bool = false
@end[verbatim]

@subsection[for_loop]{@tt{for} loop}

The @tt{for} loop iterates over a finite range of integers.  There
are two forms, one to count up, and one to count down.  The syntax of
these two operations is as follows.

$$
@begin[array, l]
@line{{@tt{for}@space v@space @tt{=}@space e_1@space @tt{to}@space e_2@space @tt{do}@space e_3@space @tt{done}}}
@line{{@tt{for}@space v@space @tt{=}@space e_1@space @tt{downto}@space e_2@space @tt{do}@space e_3@space @tt{done}}}
@end[array]
$$

The @tt{for} loops first evaluate $e_1$ and $e_2$, which must have
type @tt{int}.  The @tt{to} form evaluates the body $e_3$ for values
of $v$ counting up from $e_1$ to $e_2$, and the @tt{downto} form
evaluates the body for values counting down from $e_1$ to $e_2$.  Note
that the final value $e_2$ is @emph{included} in the evaluation.

The following code is a simpler expression for computing membership in
an array (although it is somewhat less efficient).

@begin[verbatim]
# let array_mem x a =
     let flag = ref false in
        for i = 0 to Array.length a - 1 do
           if a.(i) = x then
              flag := true
        done;
        !flag;;
val array_mem : 'a -> 'a array -> bool = <fun>
# array_mem 1 [| 3; 5; 1; 6|];;
- : bool = true
# array_mem 7 [| 3; 5; 1; 6|];;
- : bool = false
@end[verbatim]

@end[doc]
*)

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
