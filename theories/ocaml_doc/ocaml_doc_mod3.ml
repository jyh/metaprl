(* -*- Mode: text; fill-column: 100 -*- *)
doc <:doc<

   @begin[spelling]
   Arg ArgName ArgSig Elt EltSig FsetSig Int IntSet MakeFset
   SigName arg doesn elt int ll mem namespace sig struct val
   @end[spelling]

   @chapter[functors]{Functors}

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
>>

extends Base_theory

doc <:doc<

@section[functors]{Functors}

One problem with the implementation of finite sets that we have been
using is the use of the built-in @code{<} comparison operation to
compare values in the set.  The definition of the @code{<} operator is
implementation-specific, and it may not always define the exact ordering that
we want.

To fix this problem, we can define our own comparison function, but we
will need to define a separate finite set implementation for each
different element type.  For this purpose, we can use
@emph{functors}.  A functor is a @emph{function} on modules; the
function requires a module argument, and it produces a module.
Functors can be defined with the @tt{functor} keyword, or with a more
common alternate syntax.

@begin[quote]
@tt{module} @emph{Name} @tt{= functor} @emph{(ArgName} @tt{:}
@emph{ArgSig)} @tt{->}@cr
@tt{struct} @emph{implementation} @tt{end}

@tt{module} @emph{Name (Arg @tt{:} ArgSig)} @tt{=}@cr
@tt{struct} @emph{implementation} @tt{end}
@end[quote]

For the finite set example, we'll need to define an argument structure
that includes a type @tt{elt} of elements, and a comparison function @tt{compare}.
We'll have the @tt{compare} function return one of three kinds of values:

@begin[itemize]
@item{a @emph{negative} number if the first argument is smaller than
   the second,}
@item{@emph{zero} if the two arguments are equal,}
@item{a @emph{positive} number if the first argument is larger than
   the second.}
@end[itemize]

@begin[iverbatim]
module type EltSig =
sig
   type elt
   val compare : elt -> elt -> int
end
@end[iverbatim]

The finite set signature @code{FsetSig} must also be modified to used
a specific element type @tt{elt}.  Note that the set itself is no
longer polymorphic, it is defined for a specific type of elements.

@begin[iverbatim]
module type FsetSig =
sig
   type elt
   type t

   val empty : t
   val mem : elt -> t -> bool
   val insert : elt -> t -> t
end
@end[iverbatim]

Next, we redefine the set implementation as a functor.  The
implementation must be modified to include a type definition for the
@tt{elt} type, and the @tt{mem} and @tt{insert} functions must be
modified to make use of the comparison function from @code{Elt}.

@begin[iverbatim]
# module MakeFset (Elt : EltSig) =
  struct
     type elt = Elt.elt
     type color = ...
     type t =
        Node of color * t * elt * t
      | Leaf

     let empty = Leaf

     let rec mem x = function
        Leaf -> false
      | Node (_, a, y, b) ->
           let i = Elt.compare x y in
              if i < 0 then mem x a
              else if i > 0 then mem x b
              else true

     let balance = ...

     let insert x s =
        let rec ins = function
           Leaf -> Node (Red, Leaf, x, Leaf)
         | Node (color, a, y, b) as s ->
              let i = Elt.compare x y in
                 if i < 0 then balance (color, ins a, y, b)
                 else if i > 0 then balance (color, a, y, ins b)
                 else s
        in
           match ins s with  (* guaranteed to be non-empty *)
              Node (_, a, y, b) -> Node (Black, a, y, b)
            | Leaf -> raise (Invalid_argument "insert")
  end;;
module MakeFset :
  functor(Elt : EltSig) ->
    sig
      type elt = Elt.elt
      and color = | Red | Black
      and t = | Node of color * t * elt * t | Leaf
      val empty : t
      val mem : Elt.elt -> t -> bool
      val balance : color * t * elt * t -> t
      val insert : elt -> t -> t
    end
@end[iverbatim]

Note the return type.  The argument type is right: the functor takes
an argument module @tt{Elt} with signature @tt{EltSig}.  But the
returned module makes the implementation fully visible.  To fix this
problem, we need to add a type constraint using the @code{:} modifier.

@begin[iverbatim]
# module MakeFset (Elt : EltSig) : FsetSig =
  struct
     type elt = Elt.elt
     type color = ...
     type t = ...
     let empty = ...
     let rec mem x = ...
     let balance = ...
     let insert x s = ...
  end;;
module MakeFset : functor(Elt : EltSig) -> FsetSig
@end[iverbatim]

@subsection["using-functors"]{Using a functor}

To @emph{use} the module produced by the functor, we need to
@emph{apply} it to a specific module implementation the
@tt{EltSig} signature.  Let's define a comparison function for a
finite set of integers.  The comparison function is straightforward.

@begin[iverbatim]
# module Int =
  struct
     type elt = int
     let compare i j =
        if i < j then
           -1
        else if i > j then
           1
        else (* i = j *)
           0
  end;;
module Int : sig type elt = int val compare : int -> int -> int end
# Int.compare 3 5;;
- : int = -1
@end[iverbatim]

We @emph{must not} give the @tt{Int} module the signature @tt{EltSig}.
In the @tt{EltSig} signature, the @tt{elt} type is @emph{abstract}.
Since there is no way to create a value of the abstract type @tt{elt},
it would become impossible to use the @tt{compare} function, and the
module would become useless.

@begin[iverbatim]
# module Int' = (Int : EltSig);;
module Int' : EltSig
# Int'.compare 3 5;;
Characters 13-14:
This expression has type int but is here used with type Int'.elt
@end[iverbatim]

A functor is applied to an argument with the syntax
@tt{@emph{Functor_name} (@emph{Arg_name})}.  To build a finite set of
integers, we apply the @tt{MakeFset} functor to the @tt{Int} module.

@begin[iverbatim]
# module IntSet = MakeFset (Int);;
module IntSet :
  sig
    type elt = MakeFset(Int).elt
    and t = MakeFset(Int).t
    val empty : t
    val mem : elt -> t -> bool
    val insert : elt -> t -> t
  end
# IntSet.empty;;
- : IntSet.t = <abstr>
@end[iverbatim]

Note the type definitions for @tt{elt} and @tt{t}: both types are abstract.

@subsection["sharing-constraints"]{Sharing constraints}

In its current state, the @tt{IntSet} module is actually useless.
Once again, the problem is with type abstraction: the @tt{elt} type is
defined as an @emph{abstract} type in the @tt{FsetSig} signature.  The
OCaml compiler remembers that the type of elements @tt{elt} is
produced by an application of the functor, but it doesn't know that
the argument type in the @tt{Int} module was @tt{int}.

@begin[iverbatim]
# IntSet.insert 5 IntSet.empty;;
Characters 14-15:
This expression has type int but is here used with type
  IntSet.elt = MakeFset(Int).elt
@end[iverbatim]

To fix this problem, we can't add a type definition in the
@tt{FsetSig} module, since we want to be able to construct finite sets
with multiple different element types.  The only way to fix this
problem is to add a constraint on the functor type that specifies that
the @tt{elt} type produced by the functor is the @emph{same} as the
@tt{elt} type in the argument.

@subsection["proper-definition"]{An implementation that works}

These kind of type constraints are called @emph{sharing constraints}.
The argument and value of the @tt{MakeFset} functor ``share'' the same
@tt{elt} type.  Sharing constraints are defined by adding a @tt{with
type} constraint to a signature.  The corrected definition of the
@tt{MakeFset} functor is as follows.

@begin[iverbatim]
# module MakeFset (Elt : EltSig)
    : FsetSig with type elt = Elt.elt =
  struct
     type elt = Elt.elt
     type color = ...
     type t = ...
     let empty = ...
     let rec mem x = ...
     let balance = ...
     let insert x s = ...
  end;;
module MakeFset :
  functor(Elt : EltSig) ->
    sig
      type elt = Elt.elt
      and t
      val empty : t
      val mem : elt -> t -> bool
      val insert : elt -> t -> t
    end
@end[iverbatim]

The toploop now displays the correct element specification.  When we
redefine the @tt{IntSet} module, we get a working version of finite
sets of integers.

@begin[iverbatim]
# module IntSet = MakeFset (Int);;
module IntSet :
  sig
    type elt = Int.elt
    and t = MakeFset(Int).t
    val empty : t
    val mem : elt -> t -> bool
    val insert : elt -> t -> t
  end
# IntSet.empty;;
- : IntSet.t = <abstr>
# open IntSet;;
# let s = insert 3 (insert 5 (insert 1 empty));;
val s : IntSet.t = <abstr>
# mem 5 s;;
- : bool = true
# mem 4 s;;
- : bool = false
@end[iverbatim]

@docoff

@section["old-text"]{Old text}

Module signatures correspond to the signatures defined in a @code{.mli} file, and module structures
correspond to the implementations defined in a @code{.ml} file.  There is one major difference.
Each compilation unit has at most one signature, defined by the @code{.mli} file.  The module system
is more general: a single signature can be used to specify multiple structures; and a structure can
have multiple signatures.

This ability to share signatures and structures can have
important effects on code re-use.  For example, in Chapter
@refchapter[unions], we introduced three implementations of finite
sets (using unbalanced, ordered, and balanced binary trees).  All
three of these implementations can be expressed as structures having
the @emph{same} signature.  Any of the three implementations can be
used in a context that requires an implementation of finite sets.

The ability to assign multiple signatures to a structure becomes
useful in larger programs composed of multiple components each spread
over multiple files.  The structures within a program component may
make their implementations visible to one another (like a ``friend''
declaration in a C++ class, or a @tt{protected} declaration for a Java
method).  Outside the program component, a new signature may be
assigned to hide the implementation details (making them private).

The OCaml module system also includes functors, or
@emph{parameterized structures}.  A functor is a function that
computes a structure given a structure argument.  Functors provide a
simple way to generalize the implementation of a structure.

In the following sections, we'll describe the three different parts of
the module system by developing the finite set example in the context
of the module system.

>>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
