(* -*- Mode: text -*- *)
doc <:doc<

   @begin[spelling]
   Coercions Subclassing Superclassing
   fields subclassing
   superclass superclasses typecase
   @end[spelling]

   @chapter[inheritance]{Inheritance}

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2000-2005 Jason Hickey, Caltech

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
extends Base_theory
extends Ocaml_doc_comment

doc <:doc<

@begin[verbatim]
JYH: this is currently a very rough draft.
@end[verbatim]

Inheritance, in a general sense, is the the ability for one part of a
program to re-use code in another part of the program by specifying
the code to be re-used as well as any modifications that are needed.
In the context of object-oriented languages, inheritance usually means
the ability for one class to acquire methods and other attributes
from another class---in other words the first class inherits from the
second---simply by referring to the inherited class.
Normally inheritance will be transitive; if C inherits from B and B
inherits from A, then C also inherits (indirectly) from A.

Object-oriented programming languages that use static typing (not all
do) need also to describe the typing rules for objects that may be
influenced by the inheritance relationships in the program.  Normally,
this takes the form of a @emph{subtyping} relationship, written $B
@subtype A$, which specifies that a value of type $B$ may be used
anywhere where a value of type $A$ is expected.  In OCaml, as in many
other object-oriented languages, inheritance and subtyping are the
same.  That is, if class $B$ inherits from class $A$, then $B @subtype
A$, and an object of class $B$ may be used anywhere where an object of
class $A$ is expected.

Furthermore, the dual role of classes as definitions for objects and
classes as (or producing) types for object expressions has caused some
object-oriented languages to distinguish @emph{implementation
inheritance} and @emph{interface inheritance}.  @emph{Implementation
inheritance} refers to inheriting of attribute @emph{definitions}:
instance variables, methods, and sometimes other structural elements.
@emph{Interface inheritance} refers to inheriting of attribute
@emph{specifications}: types for methods (and sometimes instance
variables) and a requirement that definitions for the specified
elements be present.

The OCaml object system provides extensive support for inheritance,
including both implementation inheritance and interface inheritance,
and explicit control for cases where methods have parameters that
might be affected by inheritance.  To ensure that programs be
type-safe, the object system includes type-safe constructions for
doing type conversion up and down the inheritance hierarchy.

In this chapter we will cover the language constructs in OCaml that
support inheritance, and show code examples for standard patterns that
normally arise in programs that make use of inheritance---abstract
classes and methods, access to ``super,'' sending messages up and down
the inheritance hierarchy.  The latter part of the chapter will cover
these same items again for @emph{multiple inheritance}, where classes
inherit from more than one ``parent'' class.

@section["simple-inheritance"]{Simple inheritance}

Let's return to the example of random number generators, introduced in
the previous chapter.  All the examples in that chapter used the
linear congruential method for computing pseudo-random sequences.  The
linear method isn't the only method for generating pseudo-random
sequences, of course.  Suppose we wish to use a new quadratic method,
say $x_{n + 1} = x_n(x_n + 1) @mathrel{@bf{land}} m$, to build a new
class @code{quadratic_rng}.  Only one method (the @code{next}
method) needs to be redefined, as shown in Figure @reffigure[rng1].

@begin[figure,rng1]
@begin[center]
@begin[tabular,ll]
@line{{
@begin[minipage,3in,t]
@begin[verbatim]
class linear_rng =
  object (self)
      val a = 314159262
      val c = 1
      val m = 0x3fffffff
      val mutable x = 2
      method private next =
          x <- (x * a + c) land m
      method next_int =
          self#next;
          x
      method next_float =
          self#next;
          float_of_int x /. float_of_int m
  end;;
@end[verbatim]
@end[minipage]}
{@begin[minipage,3in,t]
@begin[verbatim]
class quadratic_rng =
   object
       inherit linear_rng
       method private next =
           x <- (x * (x + 1)) land m
   end;;

class quadratic_rng :
  object
    val mutable x : int
    val m : int
    val c : int
    val a : int
    method private next : unit
    method next_float : float
    method next_int : int
  end
@end[verbatim]
@end[minipage]}}
@end[tabular]
@end[center]
@end[figure]

The class @code{quadratic_rng} inherits from the class
@code{linear_rng}, which means that it gets all the methods and
instance variables from @code{linear_rng}.  In the figure, the
@code{quadratic_rng} also redefines the @code{next} method to use a
quadratic formula.  The new definition @emph{overrides} the previous
definition; when the @code{self#next} method is invoked, it now refers
to the quadratic computation, not the linear.

@begin[verbatim]
# let rng = new quadratic_rng;;
val rng : quadratic_rng = <obj>
# rng#next_int;;
- : int = 6
# rng#next_int;;
- : int = 42
@end[verbatim]

@subsection["type-equality"]{Type equality}

Now that we have defined a quadratic generator, we would expect that
it can be used in all the same places that a linear generator can be
used---after all, that two classes have the same methods with the same
types.  For example, let's redefine a @code{choose} function that
selects an element from an array.  Here we specify explicitly that the
@code{choose} function should take a @code{linear_rng} as an argument.

@begin[verbatim]
# let choose (rng : linear_rng) elements () =
      elements.(rng#next_int mod Array.length elements);;
val choose : linear_rng -> 'a array -> unit -> 'a = <fun>
# let g = choose (new quadratic_rng) [|"Red"; "Green"; "Blue"|];;
val g : unit -> int = <fun>
# g ();;
- : string = "Red"
...
# g ();;
- : string = "Green"
# g ();;
- : string = "Blue"
@end[verbatim]

In this case, the reason why the @code{quadratic_rng} is accepted as a
@code{linear_rng} is because the generator classes have types that are
exactly equal---they have the same methods, and each method has the
same type.

@subsection["subtyping"]{Subtyping}

In general, of course, the class type may change during inheritance.
Suppose, for example, that we decide to give the quadratic generator
an extra method.

@begin[verbatim]
# class quadratic_rng =
   object
       inherit linear_rng
       method private next =
           x <- (x * (x + 1)) land m
       method print =
           print_string ("x = " ^ string_of_int x)
   end;;

# let choose (rng : linear_rng) elements () =
    elements.(rng#next_int mod Array.length elements);;

# let g = choose (new quadratic_rng) [|"Red"; "Green"; "Blue"|];;
This expression has type quadratic_rng but
    is here used with type linear_rng
Only the first object type has a method print
@end[verbatim]

Here, the class types are no longer the same, because the class
@code{quadratic_rng} has an extra method.  The OCaml compiler rejects
use of a quadratic generator because of a type-mismatch.  In fact,
the error message mentions the name of the extra method.

OCaml takes a strict approach to subtyping.  The type
@code{quadratic_rng} is a subtype of @code{linear_rng}, but coercions
must be explicit.  That is, we must explicitly @emph{coerce} the
@code{quadratic_rng} to a @code{linear_rng} using the @code{:>}
operator, as follows.

@begin[verbatim]
# let g = choose (new quadratic_rng :> linear_rng) [|"Red"; "Green"; "Blue"|];;
val g : unit -> string = <fun>
# g ();;
- : string = "Red"
@end[verbatim]

The @code{:>} operator @emph{casts} its argument, which must have an
object type, to a supertype.  In cases where the argument type can't be
inferred, a ternary form may be used.  For example, the following
function defines a cast from @code{quadratic_rng} to
@code{linear_rng}.

@begin[verbatim]
# let linear_of_quadratic_rng rng =
     (rng : quadratic_rng :> linear_rng);;
val linear_of_quadratic_rng : quadratic_rng -> linear_rng = <fun>
@end[verbatim]

@section["abstract-classes"]{Abstract classes}

@begin[verbatim]
Outline for the rest of single-inheritance.
1. Abstract classes:
   a. Define an abstract superclass rng.
2. Variance annotations.
3. Interface inheritance
4. Lack of downcasting.
@end[verbatim]

>>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
