doc <:doc< -*- Mode: text -*-

   @begin[spelling]
   hoc cons deconstructed destructed doesn
   ll namespace obfuscation
   @end[spelling]

   @begin[doc]
   @chapter[tuples]{Tuples, Lists, and Polymorphism}
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
   @docoff
>>

extends Base_theory

doc <:doc<
   @begin[doc]
In the chapters leading up to this one, we have seen simple
expressions involving numbers, characters, strings, functions and
variables.  This language is already Turing complete---we can code
arbitrary data types using numbers and functions.  Of course, in
practice, this would not only be inefficient, it would also make it
very hard to understand our programs.  For efficient, and readable,
data structure implementations we need @emph{aggregate types}.

OCaml provides a rich set of aggregate types, including tuples, lists,
disjoint unions (also called tagged unions, or variant records),
records, and arrays.  In this chapter, we'll look at the simplest
part: tuples and lists.  We'll discuss unions in Chapter
@refchapter[unions], and we'll leave the remaining types for Chapter
@refchapter[records], when we introduce side-effects.

@section[polymorphism]{Polymorphism}

At this point, it is also appropriate to introduce
@emph{polymorphism}.  The ML languages provide @emph{parametric
polymorphism}.  That is, types may be parameterized by type
variables.  For example, the identity function in ML can be expressed
with a single function.

@begin[iverbatim]
# let identity x = x;;
val identity : 'a -> 'a = <fun>
# identity 1;;
- : int = 1
# identity "Hello";;
- : string = "Hello"
@end[iverbatim]

@emph{Type variables} are lowercase identifiers preceded by a single
quote (@code{'}).  A type variable represents an @emph{arbitrary}
type.  The typing @code{identity : 'a -> 'a} says that the
@tt{identity} function takes an argument of some arbitrary type
@code{'a} and returns a value of the same type @code{'a}.  If the
@tt{identity} function is applied to an @tt[int], then it returns an
@tt[int]; if it is applied to a @tt{string}, then it returns a
@tt{string}.  The @tt{identity} function can even be applied to
function arguments.

@begin[iverbatim]
# let succ i = i + 1;;
val succ : int -> int = <fun>
# identity succ;;
- : int -> int = <fun>
# (identity succ) 2;;
- : int = 3
@end[iverbatim]

In this case, the @code{(identity succ)} expression returns the
@code{succ} function itself, which can be applied to @code{2} to
return @code{3}.

@subsection["value-restriction"]{Value restriction}

What happens if we apply the @tt{identity} to a @emph{polymorphic}
function type?

@begin[iverbatim]
# let identity' = identity identity;;
val identity' : '_a -> '_a = <fun>
# identity' 1;;
- : int = 1
# identity';;
- : int -> int = <fun>
# identity' "Hello";;
Characters 10-17:
This expression has type string
but is here used with type int
@end[iverbatim]

This doesn't quite work as we expect.  Note the type assignment
@code{identity' : '_a -> '_a}.  The type variables @code{'_a} are now
preceded by an underscore.  These type variables specify that the
@code{identity'} function takes an argument of @emph{some} type, and
returns a value of the same type.  This is a form of delayed
polymorphism.  When we apply the @tt{identity'} function to a number,
the type @code{'_a} is assigned to be @code[int]; the @tt{identity'}
function can no longer be applied to a string.

This behavior is due to the @emph{value restriction}: for an
expression to be truly polymorphic, it must be a value.  Values are
immutable expressions that evaluate to themselves.  For example,
numbers and characters are values.  Functions are also values.
Function applications, like @code{identity identity} are @emph{not}
values, because they can be simplified (the @code{identity identity}
expression evaluates to @code{identity}).

The normal way to get around the value restriction is to use
@emph{eta-expansion}, which is the technical term for adding extra
arguments to the function.  We know that @code{identity'} is a
function; we can add its argument explicitly.

@begin[iverbatim]
# let identity' x = (identity identity) x;;
val identity' : 'a -> 'a = <fun>
# identity' 1;;
- : int = 1
# identity' "Hello";;
- : string = "Hello"
@end[iverbatim]

The new version of @code{identity'} computes the same value, but now
it is properly polymorphic.  Why does OCaml have this restriction?  It
probably seems silly, but the value restriction is a simple way to
maintain correct typing in the presence of side-effects; it would not
be necessary in a purely functional language.  We'll revisit this in
Chapter @refchapter[records].

@subsection["poly-comparison"]{Comparison with other languages}

Polymorphism can be a powerful tool.  In ML, a single identity
function can be defined that works on all types.  In a non-polymorphic
language like C, a separate identity function would have to be
defined for each type.

@begin[iverbatim]
int int_identity(int i)
{
   return i;
}

struct complex { float real; float imag; };

struct complex complex_identity(struct complex x)
{
   return x;
}
@end[iverbatim]

Another kind of polymorphism is @emph{overloading} (also called
@emph{ad-hoc} polymorphism).  Overloading allows several functions to
have the same name but different types.  When that function is
applied, the compiler selects the appropriate function by checking the
type of the arguments.  For example, in Java we could define a class
that includes several definitions of addition for different types
(note that the @code{+} operator is already overloaded).

@begin[iverbatim]
class Adder {
    static int Add(int i, int j) {
       return i + j;
    }
    static float Add(float x, float y) {
       return x + y;
    }
    static String Add(String s1, String s2) {
       return s1.concat(s2);
    }
}
@end[iverbatim]

The expression @code{Adder.Add(5, 7)} would evaluate to @code{12}, while the
expression @code{Adder.Add("Hello ", "world")} would evaluate to the string
@code{"Hello world"}.

OCaml does @emph{not} provide overloading.  There are probably two
main reasons.  One is technical: it is hard to provide both type
inference @emph{and} overloading at the same time.  For example,
suppose the @code{+} function were overloaded to work both on integers
and floating-point values.  What would be the type of the following
@code{add} function?  Would it be @code{int -> int -> int}, or
@code{float -> float -> float}?

@begin[iverbatim]
let add x y =
   x + y;;
@end[iverbatim]

The best solution would probably to have the compiler produce
@emph{two} instances of the @tt{add} function, one for integers and
another for floating point values.  This complicates the compiler, and
with a sufficiently rich type system, type inference would become
undecidable.  @emph{That} would be a problem.

The second reason for the omission is that overloading can make it
more difficult to understand programs.  It may not be obvious by
looking at the program text @emph{which} one of a function's instances
is being called, and there is no way for a compiler to check if all
the function's instances do ``similar'' things@begin[footnote]
The second reason is weaker.  Properly used, overloading reduces
namespace clutter by grouping similar functions under the same
name.  True, overloading is grounds for obfuscation, but OCaml is
already ripe for obfuscation by allowing arithmetic functions like
@tt{+} to be redefined!
@end[footnote].

@section[tuples]{Tuples}

Tuples are the simplest aggregate type.  They correspond to the
ordered tuples you have seen in mathematics, or set theory.  A
tuple is a collection of values of arbitrary types.  The syntax for a
tuple is a sequence of expressions separated by commas.  For example,
the following tuple is a pair containing a number and a string.

@begin[iverbatim]
# let p = 1, "Hello";;
val p : int * string = 1, "Hello"
@end[iverbatim]

The syntax for the type of a tuple is a @code{*} delimited list of the
types of the components.  In this case, the type of the pair is
@code{int * string}.

Tuples can be @emph{deconstructed} using pattern matching, with any of
the pattern matching constructs like @tt{let}, @tt{match}, @tt{fun},
or @tt{function}.  For example, to recover the parts of the pair in
the variables @tt{x} and @tt{y}, we might use a @tt{let} form.

@begin[iverbatim]
# let x, y = p;;
val x : int = 1
val y : string = "Hello"
@end[iverbatim]

The built-in functions @tt[fst] and @tt[snd] return the components of
a pair, defined as follows.

@begin[iverbatim]
# let fst (x, _) = x;;
val fst : 'a * 'b -> 'a = <fun>
# let snd (_, y) = y;;
val snd : 'a * 'b -> 'b = <fun>
# fst p;;
- : int = 1
# snd p;;
- : string = "Hello"
@end[iverbatim]

Tuple patterns in a function argument must be enclosed in parentheses.
Note that these functions are polymorphic.  The @tt[fst] and @tt[snd]
functions can be applied to a pair of any type @code{'a * 'b};
@tt[fst] returns a value of type @code{'a}, and @tt[snd] returns a
value of type @code{'b}.

There are no similar built-in functions for tuples with more than two
elements, but they can be defined.

@begin[iverbatim]
# let t = 1, "Hello", 2.7;;
val t : int * string * float = 1, "Hello", 2.7
# let fst3 (x, _, _) = x;;
val fst3 : 'a * 'b * 'c -> 'a = <fun>
# fst3 t;;
- : int = 1
@end[iverbatim]

Note also that the pattern assignment is @emph{simultaneous}.  The
following expression swaps the values of @tt{x} and @tt{y}.

@begin[iverbatim]
# let x = 1;;
val x : int = 1
# let y = "Hello";;
val y : string = "Hello"
# let x, y = y, x;;
val x : string = "Hello"
val y : int = 1
@end[iverbatim]

Since the components of a tuple are unnamed, tuples are most
appropriate if they have a small number of well-defined components.
For example, tuples would be an appropriate way of defining Cartesian
coordinates.

@begin[iverbatim]
# let make_coord x y = x, y;;
val make_coord : 'a -> 'b -> 'a * 'b = <fun>
# let x_of_coord = fst;;
val x_of_coord : 'a * 'b -> 'a = <fun>
# let y_of_coord = snd;;
val y_of_coord : 'a * 'b -> 'b = <fun>
@end[iverbatim]

However, it would be awkward to use tuples for defining database
entries, like the following.  For that purpose, records would be more
appropriate.  Records are defined in Chapter @refchapter[records].

@begin[iverbatim]
# (* Name, Height, Phone, Salary *)
  let jason = ("Jason", 6.25, "626-395-6568", 50.0);;
val jason : string * float * string * float =
# let name_of_entry (name, _, _, _) = name;;
val name_of_entry : 'a * 'b * 'c * 'd -> 'a = <fun>
  "Jason", 6.25, "626-395-6568", 50
# name_of_entry jason;;
- : string = "Jason"
@end[iverbatim]

@section[lists]{Lists}

Lists are also used extensively in OCaml programs.  A list contains a
sequence of values of the same type.  There are two constructors:
the @code{[]} expression is the empty list, and the $e_1 @tt{::} e_2$
expression is the @emph{cons} of expression $e_1$ onto the list $e_2$.

@begin[iverbatim]
# let l = "Hello" :: "World" :: [];;
val l : string list = ["Hello"; "World"]
@end[iverbatim]

The bracket syntax $[ e_1; @ldots; e_n ]$ is an alternate syntax for
the list containing the values computed by $e_1, @ldots, e_n$.

The syntax for the type of a list with elements of type @tt{t} is @code{t list}.
The @tt{list} type is a of a @emph{parameterized} type.  An
@code{int list} is a list containing integers, a @code{string list} is
a list containing strings, and an @code{'a list} is a list containing
elements of some type @code{'a} (but all the elements have to have the
same type).

Lists can be deconstructed using pattern matching.  For example, here is
a function that adds up all the numbers in an @code{int list}.

@begin[iverbatim]
# let rec sum = function
     [] -> 0
   | i :: l -> i + sum l;;
val sum : int list -> int = <fun>
# sum [1; 2; 3; 4];;
- : int = 10
@end[iverbatim]

These functions can also be polymorphic.  The function to check if a
value @tt{x} is in a list @tt{l} could be defined as follows.

@begin[iverbatim]
# let rec mem x l =
     match l with
        [] -> false
      | y :: l -> x = y || mem x l;;
val mem : 'a -> 'a list -> bool = <fun>
# mem 5 [1; 7; 3];;
- : bool = false
# mem "do" ["I'm"; "afraid"; "I"; "can't";
            "do"; "that"; "Dave"];;
- : bool = true
@end[iverbatim]

This function takes an argument of any type @code{'a}, and checks if
the element is in the @code{'a list}.

The standard map function, @code{List.map}, can be defined as
follows.

@begin[iverbatim]
# let rec map f = function
   [] -> []
 | x :: l -> f x :: map f l;;
val map : ('a -> 'b) -> 'a list -> 'b list = <fun>
# map succ [1; 2; 3; 4];;
- : int list = [2; 3; 4; 5]
@end[iverbatim]

The @tt{map} function takes a @emph{function} of type @code{'a -> 'b}
(this argument function takes a value of type @code{'a} and returns a
value of type @code{'b}), and a list containing elements of type
@code{'a}.  It returns a @code{'b list}.  Equivalently,

$$@tt{map}@space f@space[] [v_1; @ldots; v_n] = [f@space v_1; @ldots;
f@space v_n].$$

Lists are commonly used to represent sets of values or key-value relationships.
The @tt{List} library contains many list functions.  The
@code{List.assoc} function returns the value for a key in a list.

@begin[iverbatim]
# let entry =
     [("name", "Jason");
      ("height", "6' 3''");
      ("phone", "626-395-6568");
      ("salary", "$50")];;
val entry : (string * string) list =
  ["name", "Jason"; "height", "6' 3''";
   "phone", "626-345-9692"; "salary", "$50"]
# List.assoc "phone" entry;;
- : string = "626-395-6568"
@end[iverbatim]

Note that the comma separates the elements of the pairs in the list,
and the semicolon separates the items of the list.

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
