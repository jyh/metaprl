(*! -*- Mode: text -*-
 *
 * @begin[spelling]
 * Arg ArgName ArgSig Elt EltSig FsetSig Int IntSet MakeFset
 * SigName arg doesn elt int ll mem namespace sig struct val
 * @end[spelling]
 *
 * @begin[doc]
 * @chapter[modules]{The OCaml Module System}
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

The compilation units discussed in the Chapter @refchapter[files] are not the
only way to create modules.  OCaml provides a general module system
where modules can be created explicitly using the @code{module}
keyword.  There are three key parts in the module system:
@emph{signatures}, @emph{structures}, and @emph{functors}.

Module signatures correspond to the signatures defined in a
@code{.mli} file, and module @emph{structures} correspond to the
implementations defined in a @code{.ml} file.  There are several
differences however.  One obvious difference is that a compilation
unit can contain multiple structures and signatures.  Another, perhaps
more important difference, is that a single signature can be used to
specify multiple structures; and a structure can have multiple
@emph{signatures}.

This ability to @emph{share} signatures and structures can have
important effects on code re-use.  For example, in Chapter
@refchapter[unions], we introduced three implementations of finite
sets (using unbalanced, ordered, and balanced binary trees).  All
three of these implementations can be expressed as structures having
the @emph{same} signature.  Any of the three implementations can be
used in a context that requires an implementation of finite sets.

The ability to assign multiple signatures to a structure becomes
useful in larger programs composed of multiple components each spread
over multiple files.  The structures within a program component may
make their implementations visible to one another (like a ``friends''
declaration in a C++ class, or a @tt{protected} declaration for a Java
method).  Outside the program component, a new signature may be
assigned to hide the implementation details (making them ``private'').

The OCaml module system also includes @emph{functors}, or
@emph{parameterized} structures.  A functor is a @emph{function} that
computes a structure given a structure argument.  Functors provide a
simple way to generalize the implementation of a structure.

In the following sections, we'll describe the three different parts of
the module system by developing the finite set example in the context
of the module system.

@section[modules_signatures]{Module signatures}

A module signature is declared with a @code{module type} declaration.

@begin[center]
@tt{module type} @emph{Name} @tt{= sig} @emph{signature} @tt{end}
@end[center]

The @emph{name} of the signature must begin with an uppercase letter.
The @emph{signature} can contain any of the items that can occur in an
interface @code{.mli} file, including any of the following.

@begin[itemize]
@item{@tt{type} declarations}
@item{@tt{exception} definitions}
@item{method type declarations, using the @tt{val} keyword}
@item{@tt{open} statements to open the namespace of another signature}
@item{@tt{include} statements that include the contents of another
   signature}
@item{nested signature declarations}
@end[itemize]

Signatures can be defined in an interface, implementation, or in the
OCaml toploop.  A signature is like a type declaration---if a
@code{.mli} file defines a signature, the @emph{same} signature
must also be defined in the @code{.ml} file.

For the finite sets example, the signature should include a type
declaration for the sets, and method declarations for the @tt{empty},
@tt{mem}, and @tt{insert} methods.  For this example, we'll return to
the OCaml toploop, which will display the types of the modules we define.

@begin[verbatim]
# module type FsetSig =
  sig
     type 'a t
     val empty : 'a t
     val mem : 'a -> 'a t -> bool
     val insert : 'a -> 'a t -> bool
  end;;
module type FsetSig =
  sig
    type 'a t
    val empty : 'a t
    val mem : 'a -> 'a t -> bool
    val insert : 'a -> 'a t -> bool
  end
@end[verbatim]

The @tt{include} statements can be used to create a new signature that
@emph{extends} an existing signature.  For example, suppose we would
like to define a signature for finite sets that includes a @tt{delete}
function to remove an element of a set.  One way to be to re-type the
entire signature for finite sets followed by the @tt{delete}
declaration.  The @tt{include} statement performs this inclusion
automatically.

@begin[verbatim]
# module type FsetDSig =
  sig
     include Fset
     val delete : 'a -> 'a t -> 'a t
  end;;
module type FsetDSig =
  sig
    type 'a t
    val empty : 'a t
    val mem : 'a -> 'a t -> bool
    val insert : 'a -> 'a t -> bool
    val delete : 'a -> 'a t -> 'a t
  end
@end[verbatim]

@section[modules_structures]{Module structures}

Module structures are defined with the @tt{module} keyword.

@begin[center]
@tt{module} @emph{Name} @tt{= struct} @emph{implementation} @tt{end}
@end[center]

Once again, the module @emph{name} must begin with an uppercase
letter.  The @emph{implementation} is exactly the same as the contents
of a @code{.ml} file.  It can include any of the following.

@begin[itemize]
@item{@tt{type} definitions}
@item{@tt{exception} definitions}
@item{method definitions, using the @tt{let} keyword}
@item{@tt{open} statements to open the namespace of another module}
@item{@tt{include} statements that include the contents of another
   module}
@item{signature declarations}
@item{nested structure definitions}
@end[itemize]

Let's try this with the balanced binary tree example (the complete
definitions for the @tt{balance} and @tt{insert} functions are given
in Section @refsubsection[method_definitions].

@begin[verbatim]
# module Fset =
  struct
     type color =
        Red
      | Black

     type 'a t =
        Node of color * 'a t * 'a * 'a t
      | Leaf

     let empty = Leaf

     let rec mem x = function
        Leaf -> false
      | Node (_, a, y, b) ->
           if x < y then mem x a
           else if x > y then mem x b
           else true

     let balance = ...

     let insert x s = ...
  end;;
module Fset :
  sig
    type color = | Red | Black
    and 'a t = | Node of color * 'a t * 'a * 'a t | Leaf
    val empty : 'a t
    val mem : 'a -> 'a t -> bool
    val balance : color * 'a t * 'a * 'a t -> 'a t
    val insert : 'a -> 'a t -> 'a t
  end
# Fset.empty;;
- : 'a Fset.t = Fset.Leaf
# Fset.balance;;
- : Fset.color * 'a Fset.t * 'a * 'a Fset.t -> 'a Fset.t = <fun>
@end[verbatim]

@subsection[sig_assignment]{Assigning a signature}

Note that the default signature assigned to the structure exposes
@emph{all} of the types and functions in the structure, including the
type definitions for the @tt{color} and @code{'a t} types, as well as
the @tt{balance} function.  To assign a signature to a structure, we
include a type constraint using a @code{:} modifier of the following
form.

@begin[center]
@tt{module} @emph{Name} @tt{:} @emph{SigName} @tt{= struct} @emph{implementation} @tt{end}
@end[center]

In the finite set example, we want to assign the @code{FsetSig}
signature to the module.

@begin[verbatim]
# module Fset =
  struct
     type color =
        Red
      | Black

     type 'a t =
        Node of color * 'a t * 'a * 'a t
      | Leaf

     let empty = Leaf
     let rec mem x = ...
     let balance = ...
     let insert x s = ...
  end;;
module Fset : FsetSig
# Fset.empty;;
- : 'a Fset.t = <abstr>
# Fset.balance;;
Characters 0-12:
Unbound value Fset.balance
@end[verbatim]

When we assign this signature, the type definition for @code{'a t}
becomes @emph{abstract}, and the @tt{balance} function is no longer
visible outside the module definition.

@section[functors]{Functors}

One problem with the implementation of finite sets that we have been
using is the use of the built-in @code{<} comparison operation to
compare values in the set.  The definition of the @code{<} operator is
implementation-specific, and it may not always define the exact ordering that
we want.

To fix this problem, we can define our own comparison function, but we
will need to define a separate finite set implementation for each
different element type.  for this purpose, we can use
@emph{functors}.  A functor is a @emph{function} on modules; the
function requires a module argument, and it produces a module.
Functors can be defined with the @tt{functor} keyword, or with a more
common alternate syntax.

@begin[center]
@tt{module} @emph{Name} @tt{= functor} @emph{(ArgName} @tt{:}
@emph{ArgSig)} @tt{->}@cr
@tt{struct} @emph{implementation} @tt{end}

@tt{module} @emph{Name (Arg @tt{:} ArgSig)} @tt{=}@cr
@tt{struct} @emph{implementation} @tt{end}
@end[center]

For the finite set example, we'll need to define an argument structure
that includes a type @tt{elt} of elements, and a comparison function @tt{compare}.
We'll have the @tt{compare} function return one of three cases:

@begin[enumerate]
@item{a @emph{negative} number if the first argument is smaller than
   the second,}
@item{@emph{zero} if the two arguments are equal,}
@item{a @emph{positive} number if the first argument is larger than
   the second.}
@end[enumerate]

@begin[verbatim]
module type EltSig =
sig
   type elt
   val compare : elt -> elt -> int
end
@end[verbatim]

The finite set signature @code{FsetSig} must also be modified to used
a specific element type @tt{elt}.  Note that the set itself is no
longer polymorphic, it is defined for a specific type of elements.

@begin[verbatim]
module type FsetSig =
sig
   type elt
   type t

   val empty : t
   val mem : elt -> t -> bool
   val insert : elt -> t -> t
end
@end[verbatim]

Next, we redefine the set implementation as a functor.  The
implementation must be modified to include a type definition for the
@tt{elt} type, and the @tt{mem} and @tt{insert} functions must be
modified to make use of the comparison function.

@begin[verbatim]
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
@end[verbatim]

Note the return type.  The argument type is right: the functor takes
an argument module @tt{Elt} with signature @tt{EltSig}.  But the
returned module make the implementation fully visible.  To fix this
problem, we need to add a type constraint using the @code{:} modifier.

@begin[verbatim]
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
@end[verbatim]

@subsection[using_functor]{Using a functor}

To @emph{use} the module produced by the functor, we need to
@emph{apply} it to a specific module implementation of the
@tt{EltSig} signature.  Let's define a comparison function for a
finite set of integers.  The comparison function is simple---we can
just subtract the two arguments.

@begin[verbatim]
# module Int =
  struct
     type elt = int
     let compare = (-)
  end;;
module Int : sig type elt = int val compare : int -> int -> int end
# Int.compare 3 5;;
- : int = -2
@end[verbatim]

Note that a type constraint would not be appropriate here.  In the
@tt{EltSig} signature, the @tt{elt} type is @emph{abstract}.  The
@tt{Int} module @emph{satisfies} the @tt{EltSig} signature, but we
want to keep the @tt{elt} definition visible.

@begin[verbatim]
# module Int' = (Int : EltSig);;
module Int' : EltSig
# Int'.compare 3 5;;
Characters 13-14:
This expression has type int but is here used with type Int'.elt
@end[verbatim]

A functor is applied to an argument with the syntax
@tt{@emph{functor_name} (@emph{arg_name})}.  To build a finite set of
integers, we apply the @tt{MakeFset} functor to the @tt{Int} module.

@begin[verbatim]
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
@end[verbatim]

Note the type definitions for @tt{elt} and @tt{t}: the OCaml compiler
notes that the two types are computed from an application of the
@tt{MakeFset} functor.

@subsection[sharing_constraints]{Sharing constraints}

In its current state, the @tt{IntSet} module is actually useless.
Once again, the problem is with type abstraction: the @tt{elt} type is
defined as an @emph{abstract} type in the @tt{FsetSig} signature.  The
OCaml compiler remembers that the type of elements @tt{elt} is
produced by an application of the functor, but it doesn't know that
the argument type in the @tt{Int} module was @tt{int}.

@begin[verbatim]
# IntSet.insert 5 IntSet.empty;;
Characters 14-15:
This expression has type int but is here used with type
  IntSet.elt = MakeFset(Int).elt
@end[verbatim]

To fix this problem, we can't add a type definition in the
@tt{FsetSig} module, since we want to be able to construct finite sets
with multiple different element types.  The only way to fix this
problem is to add a constraint on the functor type that specifies that
the @tt{elt} type produced by the functor is the @emph{same} as the
@tt{elt} type in the argument.

These kind of type constraints are called @emph{sharing constraints}.
The argument and value of the @tt{MakeFset} functor ``share'' the same
@tt{elt} type.  Sharing constraints are defined by adding a @tt{with
type} constraint to a signature.  The corrected definition of the
@tt{MakeFset} functor is as follows.

@begin[verbatim]
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
@end[verbatim]

The toploop now displays the correct element specification.  When we
redefine the @tt{IntSet} module, we get a working version of finite
sets of integers.

@begin[verbatim]
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
