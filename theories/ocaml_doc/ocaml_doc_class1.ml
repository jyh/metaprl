(* -*- Mode: text -*- *)
doc <:doc<

   @begin[spelling]
   Coercions Subclassing Superclassing
   fields subclassing
   superclass superclasses typecase
   @end[spelling]

   @chapter[classes]{The OCaml Object System}

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

doc <:doc<

OCaml includes a unique object system with classes, parameterized
classes, and objects, and the usual features of inheritance and
subclassing.  Objects and classes provide a mechanism for
extensibility and code re-use, while preserving all the features we
have come to expect from OCaml, including strong typing, type
inference, and first-class functions.

@section["class-rng"]{Simple classes}

Let's begin by defining class that implements a pseudo-random number
generator.  One of the simplest of these computes a @it{linear
congruential sequence} of numbers $@left["<"] x_n @right[">"]$ obtained from
the following formula.

$$x_{n + 1} = (a x_n + c) @mathrel{@bf{mod}} m$$

There are four special numbers:

@begin[center]
@begin[tabular,cll]
@line{{$m$} {the modulus} {$0 < m$,}}
@line{{$a$} {the multiplier} {$0 @le a < m$,}}
@line{{$c$} {the increment} {$0 @le c < m$,}}
@line{{$x_0$} {the starting value, or seed} {$0 @le x_0 < m$.}}
@end[tabular]
@end[center]

For the moment, let's choose the values $a = 314159262$, $c = 1$, $X_0 = 1$, and $m = 2^{30}$.  The following program defines a class that
provides a method @code{next_int} to compute the next integer in the
sequence.

@begin[verbatim]
class linear_congruential_rng1 =
object
    val mutable x = 1
    method next_int =
        x <- (x * 314159262 + 1) land 0x3fffffff;
        x
end;;
@end[verbatim]

In OCaml, a @emph{class} defines an object, which has a collection of
values (defined with the keyword @code{val}), and methods (defined
with @code{method}).  In this example, the value $x$ represents a
number on the random sequence.  The method @code{next_int} computes the
next number of the sequence, setting $x$ to the new value, and returns
the result.  For efficiency, and numerical reasons, instead of
computing the result modulo $2^30$, the result is masked with the
integer @code{0x3fffffff} ($2^{30} - 1$).

Before the generator can be used, it must be @emph{instantiated} using
the @code{new} operation.

@begin[verbatim]
# let rng = new linear_congruential_rng1;;
val rng : linear_congruential_rng1 = <obj>
# rng#next_int;;
- : int = 314159263
# rng#next_int;;
- : int = 149901859
# rng#next_int;;
- : int = 494387611
@end[verbatim]

The @code{new} operation builds an @emph{object} from the class.
Methods in the object are invoked with the operator @code{#} and the
method name.

@subsection["objects-vs-classes"]{Objects vs. classes}

In OCaml, objects and classes are not the same.  A class defines a
template for constructing an object, but it is not an object itself.
In addition, every class has a name, while objects can
be defined and used anonymously.

@begin[verbatim]
# (object method next_int = 31 end)#next_int;;
- : int = 31
@end[iverbatim]

For the moment, the existence of a name has little significance.
However, as we will see in the next chapter, the name is required for
defining inheritance.  That is, it is possible to inherit from
classes, but not objects.  For this reason, we will usually be
defining classes, rather than anonymous objects.

@section["class-parameters"]{Parameterized classes}

The class @code{linear_congruential_rng1} is somewhat limited, because
the parameters for the random sequence are hard-coded.  It is also
possible to parameterize a class.  The syntax is much the same as for
defining a function; the parameters are listed after the class name.

@begin[verbatim]
# class linear_congruential_rng a c seed =
object
    val mutable x = seed
    method next_int =
        x <- (x * a + c) land 0x3fffffff;
        x
end;;
class linear_congruential_rng :
int -> int -> int ->
   object val mutable x : int method next_int : int end
@end[verbatim]

A parameterized class is essentially a function that computes a
class.  For example, we can obtain a class that is equivalent to the
original generator by applying the parameterized class to the original
arguments.

@begin[verbatim]
# class linear_congruential_rng1 = linear_congruential_rng 314159262 1 1;;
class linear_congruential_rng1 : linear_congruential_rng
# let rng = new linear_congruential_rng1;;
val rng : linear_congruential_rng1 = <obj>
# rng#next_int;;
- : int = 314159263
# rng#next_int;;
- : int = 149901859
@end[verbatim]

When given a parameterized class, the @code{new} operator returns a
function that computes an object given arguments for the parameters.

@begin[verbatim]
# new linear_congruential_rng;;
- : int -> int -> int -> linear_congruential_rng = <fun>
# let rng = new linear_congruential_rng 31415926 1 1;;
val rng : linear_congruential_rng = <obj>
# rng#next_int;;
- : int = 31415927
# rng#next_int;;
- : int = 575552731
@end[verbatim]

The function produced by @code{new} is the same as any other function;
it is a value that can be passed as an argument, stored in a data
structure, or partially applied.  For example, the
@code{linear_congruential_rng} takes three arguments, $a$, $c$, and
the initial seed.  If we want a particular generator with fixed values
for $a$ and $c$, and only allow the seed to vary, we can perform a
partial application.

@begin[verbatim]
# let rng_from_seed = new linear_congruential_rng 314159262 1;;
val rng_from_seed : int -> linear_congruential_rng = <fun>
# let rng = rng_from_seed 17355;;
val rng : linear_congruential_rng = <obj>
# rng#next_int;;
- : int = 846751563
# rng#next_int;;
- : int = 411455563
@end[verbatim]

@section["class-self"]{Self references and private methods}

So far, we have been dealing with objects that have one method.  It is
possible, of course, to define objects with more than one method.  For
example, in addition to generating integers, we might also want to
generate floating-point numbers uniformly distributed between $0$ and
$1$.  It seems easy enough---we can define a new method
@code{next_float} that computes the next random number, and divides it
by the modulus $m$.

@begin[verbatim]
# class linear_congruential_rng a c seed =
  object
    val mutable x = seed
    method next_int =
        x <- (x * a + c) land 0x3fffffff;
        x
    method next_float =
        x <- (x * a + c) land 0x3fffffff;
        (float_of_int x) /. (float_of_int 0x3fffffff)
  end;;
class linear_congruential_rng : ...
# let rng = new linear_congruential_rng 314159262 1 1;;
val rng : linear_congruential_rng = <obj>
# rng#next_float;;
- : float = 0.292583613928950936
# rng#next_float;;
- : float = 0.139606985393545574
@end[verbatim]

This is suboptimal of course.  We see that the @code{next_int} and
@code{next_float} methods are duplicating the code for generating
random numbers.  What we should do is move the shared code into a
shared method, called @code{next}, that computes the next number in
the sequence.

To do so, we will need to give the object a name, so that the
@code{next} method can be called from the @code{next_int} and
@code{next_float} methods.  Syntactically, this is performed by
specifying the object name in parentheses after the @bf{object}
keyword (the name can be an arbitrary lowercase identifier, but the
usual choice is @bf{self}).  Let's rewrite the new generator.

@begin[verbatim]
class linear_congruential_rng a c seed =
object (self)
    val mutable x = seed
    method next =
        x <- (x * a + c) land 0x3fffffff
    method next_int =
        self#next;
        x
    method next_float =
        self#next;
        (float_of_int x) /. (float_of_int 0x3fffffff)
end;;
@end[verbatim]

As a final step, the shared method @code{next} is really a ``private''
method, used to implement @code{next_int} and @code{next_float}.  It
is unlikely that we intend it to be called directly.  Methods of this
kind can be marked with the keyword @bf[private] after the @bf[method]
keyword, to make them inaccessible outside the object.

@begin[verbatim]
# class linear_congruential_rng a c seed =
  object (self)
      val mutable x = seed
      method private next =
          x <- (x * a + c) land 0x3fffffff
      method next_int = self#next; x
      method next_float = self#next; ...
  end;;
class linear_congruential_rng : ...
# rng#next_float;;
- : float = 0.292583613928950936
# rng#next;;
This expression has type linear_congruential_rng
It has no method next
@end[verbatim]

@section["class-initializers"]{Class initializers}

Unlike many other object-oriented languages, OCaml does not provide
explicit constructors.  With parameterized classes, there is less of a
need, since the initial object can be often computed from the
parameters.  However, there are times when it is useful or necessary
to perform a computation at object creation time.

There are two ways to specify initializers, as @bf{let}-definitions
that are evaluated before the object is created, or as anonymous
@bf{initializer} methods that are evaluated after the object is
created.

@subsection["let-initializers"]{Let-initializers}

Let-initializers are defined as the initial part of a class
definition.  Using our example, suppose we wish to define a random
number generator that produces either 1) a canonical sequence starting
from a standard seed, or 2) a sequence with a random initial seed.
Our new generator will take a Boolean argument, and use a
let-definition to choose between the cases.  For the latter case,
we'll use the current time of day as the seed.
@footnote{Note that this
example uses the @tt{Unix.gettimeofday} function.  To run the
example in the toploop, you need to pass the @tt{Unix} library using
the command @tt{ocaml unix.cma}.}

@begin[verbatim]
# class new_rng randomize_seed =
  let a, c, m = 314159262, 1, 0x3fffffff in
  let seed =
      if randomize_seed
      then int_of_float (Unix.gettimeofday ())
      else 1
  in
  let normalize x = (float_of_int x) /. (float_of_int m) in
  object (self)
      val mutable x = seed
      method private next =
          x <- (x * a + c) land m
      method next_int =
          self#next;
          x
      method next_float =
          self#next;
          normalize x
  end;;
class new_rng : ...
# let rng = new new_rng true;;
val rng : new_rng = <obj>
# rng#next_int;;
- : int = 1025032669
@end[verbatim]

Notice that we are also defining the initial parameters $a$, $c$, and
$m$ symbolically, as well as a normalization function for producing
the floating-point results.

@subsection["method-initializers"]{Anonymous initializer methods}

Let-initializers are evaluated before an object is created.  Sometimes
it is also useful to evaluate an initializer after the object is
created.  For example, supposed we wish to skip an initial prefix of
the random number sequence, and we are given the length of the initial
prefix.  While we could potentially pre-compute the initial values for
the generator, it is much easier to construct the generator without
skipping, and then remove the initial prefix before returning the
object.

@begin[verbatim]
class skip_rng skip =
  let a, c, m, seed = 314159262, 1, 0x3fffffff, 1 in
  object (self)
      val mutable x = seed
      method private next =
          x <- (x * a + c) land m
      method next_int = self#next; x
      initializer
          for i = 1 to skip do
              self#next
          done;
          Printf.printf "rng state: %d\n" x
  end;;
class skip_rng : ...
# let rng = new skip_rng 10;;
rng state: 888242763
val rng : skip_rng = <obj>
# rng#next_int;;
- : int = 617937483
# let rng11 = new skip_rng 11;;
rng state: 617937483
val rng11 : skip_rng = <obj>
@end[verbatim]

@section["class_polymorphism"]{Polymorphism}

Classes and objects may also include polymorphic values and methods.
As we have seen in the examples so far, the types of methods and
values are automatically inferred.  Very little changes when
polymorphism is introduced, but it will be necessary to introduce a
small number of annotations.

One common application of random number generators is to choose from a
finite set of values.  That is, instead of returning a number, the
generator should return a value, chosen randomly, from a prespecified
set.  The type of elements of the set is unimportant to the choice of
element, of course, so the generator should be polymorphic.

As an initial attempt, we can define a generator that takes an array
of elements as a parameter.  The @code{choose} method will then select
from this set of elements.

@begin[verbatim]
# class choose_rng elements =
    let a, c, m, seed = 314159262, 1, 0x3fffffff, 1 in
    let length = Array.length elements in
    object (self)
        val mutable x = seed
        method private next =
            x <- (x * a + c) land m
        method choose =
            self#next;
            elements.(x mod length)
    end;;
Some type variables are unbound in this type:
  class choose_rng : 'a array -> ...
@end[verbatim]

Unfortunately, this definition is rejected by the compiler because
``Some type variables are unbound.''  There are two rules to follow
when defining a polymorphic object.

@begin[enumerate]
@item{{All type parameters must be listed between square brackets after the @bf{class} keyword (for example, as @code{['a]}).}}
@item{{Explicit types must be specified for methods that return values of polymorphic type.}}
@end[enumerate]

In our example, the @code{elements} array is polymorphic, and the
@code{choose} method returns a value of polymorphic type, so the
example can be fixed as follows.

@begin[verbatim]
class ['a] choose_rng elements =
  let a, c, m, seed = 314159262, 1, 0x3fffffff, 1 in
  let length = Array.length elements in
  object (self)
      val mutable x = seed
      method private next =
          x <- (x * a + c) land m
      method choose : 'a =
          self#next;
          elements.(x mod length)
  end;;
class ['a] choose_rng : ...
# let rng = new choose_rng [|"Red"; "Green"; "Blue"|];;
val rng : string choose_rng = <obj>
# rng#choose;;
- : string = "Red"
# rng#choose;;
- : string = "Green"
# rng#choose;;
- : string = "Blue"
# rng#choose;;
- : string = "Green"
# let rng = new choose_rng [|1.1; 2.2; 3.14; 4.4; 5.5|];;
val rng : float choose_rng = <obj>
# rng#choose;;
- : float = 5.5
# rng#choose;;
- : float = 3.14
@end[verbatim]

@subsection["polymorphic-methods"]{Polymorphic methods}

A small complication arises for methods where the arguments are
polymorphic.  For example, instead of defining the set of elements are
a class parameter, suppose we pass the element array as an argument to
the @code{choose} method.  Following the rules given in the previous section,
we will have to specify a type for the @code{choose} method.

@begin[verbatim]
class ['a] choose_rng =
  let a, c, m, seed = 314159262, 1, 0x3fffffff, 17 in
  object (self)
      val mutable x = seed
      method private next =
          x <- (x * a + c) land m
      method choose (elements : 'a array) : 'a =
          self#next;
          elements.(x mod Array.length elements)
  end;;
# let rng = new choose_rng;;
val rng : '_a choose_rng = <obj>
# rng#choose [|1; 2; 3|];;
- : int = 1
# rng#choose [|1; 2; 3|];;
- : int = 2
# rng#choose [|"Red"; "Green"; "Blue"|];;
This expression has type string array but is here used with type int array
@end[verbatim]

Unfortunetely, while the object is polymorphic, it is polymorphic at only one type!

---- JYH: ran out of time, but I want to give this example ---

Solution.

@begin[verbatim]
class choose_rng =
  let a, c, m, seed = 314159262, 1, 0x3fffffff, 17 in
  object (self)
      val mutable x = seed
      method private next =
          x <- (x * a + c) land m
      method choose : 'a. 'a array -> 'a = fun elements ->
          self#next;
          elements.(x mod Array.length elements)
  end;;
class choose_rng : ...
# let rng = new choose_rng;;
val rng : choose_rng = <obj>
# rng#choose [|1; 2; 3|];;
- : int = 1
# rng#choose [|"Red"; "Green"; "Blue"|];;
- : string = "Green"
@end[verbatim]

>>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
