(*!
 * @begin[spelling]
 * Coercions Subclassing Superclassing
 * instanceof int fields pos subclassing
 * superclass superclasses typecase val
 * @end[spelling]
 *
 * @begin[doc]
 * @chapter[classes]{The OCaml Object System}
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
@begin[doc]

OCaml includes a unique object system with classes, parameterized
classes, and objects, and the usual features of inheritance and
subclassing.  Objects are perhaps not as frequently used in OCaml as
in other languages like C++ or Java, because the module system
provides similar features for code re-use.  However, classes and
objects are often appropriate in programs where extensibility is
desirable.

@section[basic_classes]{The basic object system}

The OCaml object system differs in one major way from the classes
defined in many other languages: the object system includes both class
@emph{types} as well as class @emph{expressions}.  The two are
separate, just as module signatures are separate from module
structures.  There are three construct in the OCaml object system:
class type are signatures for classes, classes are initial
specifications for objects, and objects are instances of classes
created with the @tt{new} keyword.

@subsection[class_types]{Class types}

A class type is defined using a @tt{class type} definition.  The syntax of
a class type declaration is as follows.

@begin[center]
@tt{class type} @emph{name} @tt{= object} @emph{declarations} @tt{end}
@end[center]

The @emph{name} of the class type should begin with a lowercase letter
or an underscore.  The declarations can include any of the following.

@begin[itemize]
@item{Inheritance directives with the @tt{inherit} keyword.}
@item{Values, declared with the @tt{val} keyword.}
@item{Methods, declared with the @tt{method} keyword.}
@item{Type constraints, declared with the @tt{constraint} keyword.}
@end[itemize]

To illustrate the object system, let's use the canonical object
example: a one-dimensional movable point.  The point should have
methods to return and modify the position of the point.

The class type for the point includes two methods: one to @tt{get} the
position of the point, and another to @tt{set} the position of the
point.  We will also include a@tt{reset} function to return the point to
the origin.

@begin[verbatim]
# class type point_type =
  object
     method get : int
     method set : int -> unit
     method reset : unit
  end;;
class type point_type = object
    method get : int
    method set : int -> unit
    method reset : unit
end
@end[verbatim]

@subsection[class_expressions]{Class expressions}

A class expression gives the definition of a class.  The syntax for an
class expression uses the @tt{class} keyword.

@begin[center]
@tt{object} @emph{implementation} @tt{end}
@end[center]

The implementation can include any of the following.

@begin[itemize]
@item{Values, defined with the @tt{val} keyword.}
@item{Methods, defined with the @tt{method} keyword.}
@item{Type constraints, defined with the @tt{constraint} keyword.}
@item{Initializers, defined with the @tt{initializer} keyword.}
@end[itemize]

We can build a class of the @tt{point_type} class type by implementing
each of the fields in the class type.  To implement the point, we will
need to include a @tt{pos} field that specifies the position of the
point.  The @tt{get} method should return the @tt{pos} value, and the
@tt{move} method should add an offset to the position.

@begin[verbatim]
# class point =
  object
     val mutable pos = 0
     method get = pos
     method set pos' = pos <- pos'
     method reset = pos <- 0
  end;;
class point : object
   val mutable pos : int
   method get : int
   method reset : unit
   method set : int -> unit
end
@end[verbatim]

The @code{pos <- pos + off} is a @emph{side-effect}: the value of
@tt{pos} is updated by adding the offset argument.

Note that the @tt{pos} field is @emph{visible} in the class type.  To
get the correct class type, we need to add a type constraint.

@begin[verbatim]
# class point : point_type =
  object
     val mutable pos = 0
     method get = pos
     method set pos' = pos <- pos'
     method reset = pos <- 0
  end;;
class point : point_type
@end[verbatim]

Class expressions are templates, like function bodies.  The
expressions in a class expression are not evaluated when the class is
defined; they are evaluated when the class is instantiated as an
object.

@subsection[objects]{Objects}

Objects are the values created from classes using the @tt{new}
keyword.  The methods in the object can be accessed by using the
@code{#} operator.

@begin[verbatim]
# let p = new point;;
val p : point = <obj>
# p#get;;
- : int = 0
# p#set 7;;
- : unit = ()
# p#get;;
- : int = 7
# let p2 = new point;;
val p2 : point = <obj>
# p2#get;;
- : int = 0
@end[verbatim]

@subsection[parameterized_classes]{Parameterized class expressions}

Class expressions can be parameterized in OCaml, using a @tt{fun}
expression.  For example, suppose we want to specify the initial
position of the point as an argument to the class expression.

@begin[verbatim]
# class make_point_class (initial_pos : int) =
     object
        val mutable pos = initial_pos
        method get = pos
        method set pos' = pos <- pos'
        method reset = pos <- 0
     end;;
class make_point_class : int ->
   object
      val mutable pos : int
      method get : int
      method reset : unit
      method set : int -> unit
   end
@end[verbatim]

We have to constrain the argument @tt{initial_pos} to be an @tt{int}:
otherwise the object would be polymorphic.  Specific classes can be
defined by application.

@begin[verbatim]
# class point7 = make_point_class 7;;
class point7 : make_point_class
# let p = new point7;;
val p : point7 = <obj>
# p#get;;
- : int = 7
# p#reset;;
- : unit = ()
# p#get;;
- : int = 0
@end[verbatim]

A parameterized class can also include @tt{let} definitions in the
function body.  For example, we can lift the @tt{pos} field out of the
class and use a reference cell instead.

@begin[verbatim]
# class make_point_class (initial_pos : int) =
     let pos = ref initial_pos in
        object
           method get = !pos
           method set pos' = pos := pos'
           method reset = pos := 0
        end;;
class make_point_class : int ->
   object
      method get : int
      method reset : unit
      method set : int -> unit
   end
@end[verbatim]

The body of the @tt{class} definition is not evaluated initially---it
is evaluated at object instantiation time.  All @tt{point} objects will
have separate positions.

@begin[verbatim]
# let p1 = new point7;;
val p1 : point7 = <obj>
# let p2 = new point7;;
val p2 : point7 = <obj>
# p1#set 5;;
- : unit = ()
# p2#get;;
- : int = 7
@end[verbatim]

@section[class_polymorphism]{Polymorphism}

Class types, class expressions, and methods can also be polymorphic.
For example, consider the parameterized class @code{make_point_class}
we just defined.  If we do not constrain the type of argument, we get
a type of reference cells.  The syntax of a polymorphic class includes
the type parameters in square brackets after the @tt{class} keyword.

@begin[verbatim]
# class ['a] make_ref_cell (x : 'a) =
  object
     val mutable contents = x
     method get = contents
     method set x = contents <- x
  end;;
class ['a] make_ref_cell :
  'a ->
  object
    val mutable contents : 'a
    method get : 'a
    method set : 'a -> unit
  end
# class int_ref = [int] make_ref_cell 0;;
class int_ref : [int] make_ref_cell
# let p = new int_ref;;
val p : int_ref = <obj>
# p#set 7;;
- : unit = ()
# p#get;;
- : int = 7
# class string_ref = [string] make_ref_cell "";;
class string_ref : [string] make_ref_cell
# let s = new string_ref;;
val s : string_ref = <obj>
# s#set "Hello";;
- : unit = ()
# s#get;;
- : string = "Hello"
@end[verbatim]

@section[inheritance]{Inheritance}

Inheritance allows classes to be defined by extension.  For example,
suppose we wish to define a new @tt{point} class that includes a
@tt{move} method that moves the point by a relative offset.  The
@tt{move} method can be defined using the @tt{get} and @tt{set}
methods.  To be able to access these methods, we need a @emph{self}
parameter (like the @tt{this} object in C++ or Java).

The self parameter is defined after the @tt{object} keyword.  We make
a new class @tt{movable_point} using the @tt{inherit} keyword to
inherit the @tt{point} class definition.

@begin[verbatim]
# class movable_point =
  object (self)
     inherit point
     method move off =
        self#set (self#get + off)
  end;;
class movable_point :
  object
    method get : int
    method move : int -> unit
    method reset : unit
    method set : int -> unit
  end
# let p = new movable_point;;
val p : movable_point = <obj>
# p#set 7;;
- : unit = ()
# p#get;;
- : int = 7
# p#move 5;;
- : unit = ()
# p#get;;
- : int = 12
@end[verbatim]

@subsection[multiple_inheritance]{Multiple inheritance}

Classes can also be defined by inheriting from multiple classes.  For
example, let's define a point class that also has a color.  The
@tt{color} class can be defined in the normal way.

@begin[verbatim]
# type color = Black | Red | Green | Blue;;
type color = | Black | Red | Green | Blue
# class color =
  object
     val mutable color = Black
     method get_color = color
     method set_color color' = color <- color'
     method reset = color <- Black
  end;;
class color :
  object
    val mutable color : color
    method get_color : color
    method reset : unit
    method set_color : color -> unit
  end
# let c = new color;;
val c : color = <obj>
# c#set_color Green;;
- : unit = ()
# c#get_color;;
- : color = Green
@end[verbatim]

To define a colored point we @tt{inherit} from both classes.  Objects
in this class will have the methods and values defined in both classes.

@begin[verbatim]
# class colored_point =
  object
     inherit point
     inherit color
  end;;
Characters 63-74:
Warning: the following methods are overriden
  by the inherited class: reset
class colored_point :
  object
    val mutable color : color
    method get : int
    method get_color : color
    method reset : unit
    method set : int -> unit
    method set_color : color -> unit
  end
# let cp = new colored_point;;
val cp : colored_point = <obj>
# cp#get;;
- : int = 0
# cp#get_color;;
@end[verbatim]

Note that the compiler produced a warning message when the colored
point is created.  The @tt{point} and @tt{color} @emph{both}
define a method called @tt{reset}.  Which definition does the colored
point use?

@begin[verbatim]
# cp#set 7;;
- : unit = ()
# cp#set_color Red;;
- : unit = ()
# cp#reset;;
- : unit = ()
# cp#get;;
- : int = 7
# cp#get_color;;
- : color = Black
@end[verbatim]

As usual, the compiler chooses the @emph{last} definition of the
method.

The correct version of the colored point should call @emph{both} the
@tt{point} and @tt{color} @tt{reset} functions.  The
@code{colored_point} method must override the definition.  To do this,
we need to include a name for the object in each of the @tt{inherit}
declarations.

@begin[verbatim]
class colored_point =
  object
      inherit point as p
      inherit color as c
      method reset =
         p#reset;
         c#reset
  end;;
Characters 64-69:
Warning: the following methods are overriden by the inherited class:
  reset
class colored_point :
  object
    val mutable color : color
    val mutable pos : int
    method get : int
    method get_color : color
    method reset : unit
    method set : int -> unit
    method set_color : color -> unit
  end
# let cp = new colored_point;;
val cp : colored_point = <obj>
# cp#set 5;;
- : unit = ()
# cp#set_color Red;;
- : unit = ()
# cp#reset;;
- : unit = ()
# cp#get;;
- : int = 0
# cp#get_color;;
- : color = Black
@end[verbatim]

The compiler still produces a warning message, but this time the
@tt{reset} method works correctly.

@subsection[virtual_methods]{Virtual methods}

Virtual methods can be used to postpone the implementation of methods
for definition in subclasses.  For example, suppose we wish to make a
point that includes a method @tt{move} to move the object by a
relative offset.  One way would be to inheritance to define a new
class @code{movable_point} based on the @tt{point} class.  Another,
more general, way is to define a separate @tt{movable} class that can
be combined by multiple inheritance with any class that implements
the @tt{get} and @tt{set} methods.  This class must be declared as
@tt{virtual} because it can't be instantiated (the @tt{get} and
@tt{set} methods are not implemented).

@begin[verbatim]
# class virtual movable =
  object (self)
     method virtual get : int
     method virtual set : int -> unit
     method move off =
        self#set (self#get + off)
  end;;
class virtual movable :
  object
    method virtual get : int
    method move : int -> unit
    method virtual set : int -> unit
  end
# let m = new movable;;
Characters 8-19:
One cannot create instances of the virtual class movable
@end[verbatim]

Now to create the class @code{movable_point}, we combine the classes
by multiple inheritance.

@begin[verbatim]
# class movable_point =
  object
     inherit point
     inherit movable
  end;;
class movable_point :
  object
    val mutable pos : int
    method get : int
    method move : int -> unit
    method reset : unit
    method set : int -> unit
  end
# let p = new movable_point;;
val p : movable_point = <obj>
# p#set 7;;
- : unit = ()
# p#move 5;;
- : unit = ()
# p#get;;
- : int = 12
@end[verbatim]

Note that a @tt{virtual} method in OCaml does not mean the same thing
as a @tt{virtual} declaration in C++.  In C++, the @tt{virtual}
declaration means that a method can be overridden in subclasses.  In
OCaml, all methods are virtual in this sense.  The OCaml @tt{virtual}
declaration just means that the method definition is omitted.

@subsection[subclassing]{Subclassing}

The @tt{inherit} declarations in a class definition define an
inheritance hierarchy.  In OCaml an object can be coerced to a class
type of any of its ancestors.  Coercions in OCaml must be made
explicitly using the @code{:>} operator, which requires two class types: the
type of the object, and the type of the object after the coercion.

@begin[verbatim]
# let p = (cp : colored_point :> point);;
val p : point = <obj>
# p#get;;
- : int = 0
# p#get_color;;
Characters 0-1:
This expression has type point
It has no method get_color
@end[verbatim]

If the class type can be inferred, the first type can be omitted.

@begin[verbatim]
# let p = (cp :> point);;
val p : point = <obj>
@end[verbatim]

In OCaml, objects can also be coerced to any class type that has fewer
methods.  For example, suppose we want a ``read only'' colored point
without the @tt{set} and @tt{set_color} methods.

@begin[verbatim]
# class type read_only_point =
  object
     method get : int
     method get_color : color
  end;;
class type read_only_point =
   object
      method get : int
      method get_color : color
   end
# let ro_p = (cp : colored_point :> read_only_point);;
val ro_p : funny_point = <obj>
# ro_p#get;;
- : int = 0
# ro_p#get_color;;
- : color = Red
# ro_p#set 5;;
Characters 0-4:
This expression has type read_only_point
It has no method set
@end[verbatim]

@subsection[superclassing]{Superclassing, or @tt{typecase}}

In OCaml, there is no operator to coerce an object to a superclass
(there is no ``typecase'' operator, or @tt{instanceof} predicate like
in Java).  So for instance, once we coerce a @code{colored_point} to a
@code{point}, there is no corresponding operator for recovering the
@code{colored_point}.

This kind of problem can arise frequently in some contexts, especially
when @emph{binary} functions are defined over two objects.  For
example, suppose we wish to implement an equality relation on points.
The @code{point_equal} function should take two objects.  If both
objects have type @tt{point}, and both have the same position, the
@code{point_equal} function should return @tt{true}.  If both are
@code{colored_points}, and have the same position and color, it should
also return @tt{true}.  Otherwise, it should return @tt{false}.

How can we define this function?  One thing is clear, the
@code{point_equal} function must have type
@code{point -> point -> bool}
because the type of point is not known beforehand.  If the argument is
of type @tt{point}, how can we tell if it is actually a
@code{colored_point}?

The easiest way to solve this problem is to use a ``trick.''  For each
class, we add a new method that uses an @emph{exception} to return the
actual value.  We will call this method @tt{typecase}, and it will have type
@tt{unit} (since it returns the result by exception).  The @tt{point}
class implements the @tt{typecase} method as follows.

@begin[verbatim]
# class type point_type =
  object
     method get : int
     method set : int -> unit
     method reset : unit
     method typecase : unit
  end;;
class type point_type =
  object
    method get : int
    method reset : unit
    method set : int -> unit
    method typecase : unit
  end
# exception Point of point_type;;
exception Point of point_type
# class point =
  object (self)
     val mutable pos = 0
     method get = pos
     method set pos' = pos <- pos'
     method reset = pos <- 0
     method typecase = raise (Point (self :> point_type))
  end;;
              class point :
  object
    val mutable pos : int
    method get : int
    method reset : unit
    method set : int -> unit
    method typecase : unit
  end
@end[verbatim]

The @tt{typecase} method raises the @tt{Point} exception.  Note that
the @tt{self} parameter must be coerced to @code{point_type}.

For the @code{colored_point}, we perform a similar operation.  First,
we define the type of colored points, and the exception.

@begin[verbatim]
# class type colored_point_type =
  object
     inherit point
     inherit color
  end;;
class type colored_point_type =
  object
    val mutable color : color
    val mutable pos : int
    method get : int
    method get_color : color
    method reset : unit
    method set : int -> unit
    method set_color : color -> unit
    method typecase : unit
  end
# exception ColoredPoint of colored_point_type;;
exception ColoredPoint of colored_point_type
@end[verbatim]

Next, we define the class, and override the @tt{typecase} method.

@begin[verbatim]
# class colored_point =
  object (self)
      inherit point as p
      inherit color as c
      method reset =
         p#reset;
         c#reset
      method typecase =
         raise (ColoredPoint (self :> colored_point_type))
  end;;
Characters 77-82:
Warning: the following methods are overriden by the inherited class:
  reset
class colored_point :
  object
    val mutable color : color
    val mutable pos : int
    method get : int
    method get_color : color
    method reset : unit
    method set : int -> unit
    method set_color : color -> unit
    method typecase : unit
  end
@end[verbatim]

Now, the @tt{typecase} method can be used to determine the class type
of a point.

@begin[verbatim]
# let p1 = new point;;
val p1 : point = <obj>
# let p2 = new colored_point;;
val p2 : colored_point = <obj>
# let p3 = (p2 :> point);;
val p3 : point = <obj>
# p1#typecase;;
Uncaught exception: Point(_)
# p2#typecase;;
Uncaught exception: ColoredPoint(_)
# p3#typecase;;
Uncaught exception: ColoredPoint(_)
@end[verbatim]

At this point, we can define the @code{point_print} printing function.

@begin[verbatim]
# let point_print p =
     try p#typecase with
        Point p ->
           printf "Point: position = %d\n" p#get
      | ColoredPoint p ->
          let color =
             match p#get_color with
                Black -> "black"
              | Red -> "red"
              | Green -> "green"
              | Blue -> "blue"
          in
             printf "ColoredPoint: position = %d, color = %s\n" p#get color
      | _ ->
          raise (Invalid_argument "point_print");;
val point_print : < typecase : unit; .. > -> unit = <fun>
# p1#set 7;;
- : unit = ()
# p2#set_color Green;;
- : unit = ()
# List.iter point_print [p1; (p2 :> point); p3];;
Point: position = 7
ColoredPoint: position = 0, color = green
ColoredPoint: position = 0, color = green
- : unit = ()
@end[verbatim]

There are two things to note.  First, the @code{point_print} function
takes @emph{any} object with a @tt{typecase} method---no just points.
Second, we include a default exception case: if the @tt{typecase}
method returns some other exception, the argument is invalid.

@section[functional_object]{Functional objects}

In all of the examples we have given so far, the methods work by
side-effect.  OCaml can also be used to implement @emph{functional}
objects, where method updates produce new values by copying the self
object.  The syntax for a functional update uses the

@begin[verbatim]
{< ... >}
@end[verbatim]

notation to produce a copy of the current object with @emph{the same
type} as the current object, with updated fields.  The use of the update operator is
important---it is the only way to preserve the current object's type.

Let's build a functional version of points.  We include the @tt{pos}
field, which the @tt{set} method replaces.

@begin[verbatim]
# class point =
  object
     val pos = 0
     method get = pos
     method set pos' = {< pos = pos' >}
  end;;
class point :
  object ('a)
     val pos : int
     method get : int
     method set : int -> 'a
  end
# let p1 = new point;;
val p1 : point = <obj>
# p1#get;;
- : int = 0
# let p2 = p1#set 5;;
val p2 : point = <obj>
# p2#get;;
- : int = 5
@end[verbatim]

Note the type of the @code{set} method: on an object of type
@code{'a}, it takes an integer argument, and returns a new object of
type @code{'a}.

The @code{color} class can also be modified so that it is functional.

@begin[verbatim]
# class color =
  object
     val color = Black
     method get_color = color
     method set_color color' = {< color = color' >}
     method reset = {< color = Black >}
  end;;
class color :
  object ('a)
    val color : color
    method get_color : color
    method reset : 'a
    method set_color : color -> 'a
  end
@end[verbatim]

What about the @code{colored_point} example?  For the @code{reset}
function, we need to invoke the @tt{reset} method from both the
@code{point} and @code{color} superclasses.  There is no syntax to do
this directly; for this purpose, we will need to make use of
@tt{private} methods, so that we can name the @tt{reset} functions.

@begin[verbatim]
# class colored_point =
  object (self)
     inherit point as p
     inherit color as c
     method private p_reset = p#reset
     method private c_reset = c#reset
     method reset = self#p_reset#c_reset
  end;;
Characters 75-80:
Warning: the following methods are overriden by the inherited class:
  reset
class colored_point :
  object ('a)
    val color : color
    val pos : int
    method c_reset : 'a
    method get : int
    method get_color : color
    method private p_reset : 'a
    method reset : 'a
    method set : int -> 'a
    method set_color : color -> 'a
  end
@end[verbatim]

The resulting object has the expected behavior.

@begin[verbatim]
# let p1 = new colored_point;;
val p1 : colored_point = <obj>
# let p2 = p1#set 7;;
val p2 : colored_point = <obj>
# let p3 = p2#set_color Blue;;
val p3 : colored_point = <obj>
# p3#get;;
- : int = 7
# p3#get_color;;
- : color = Blue
# p2#get_color;;
- : color = Black
# let p4 = p3#reset;;
val p4 : colored_point = <obj>
# p4#get;;
- : int = 0
# p4#get_color;;
- : color = Black
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
