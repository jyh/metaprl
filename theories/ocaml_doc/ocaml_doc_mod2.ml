(* -*- Mode: text -*- *)
doc <:doc<

   @begin[spelling]
   Arg ArgName ArgSig Elt EltSig FsetSig Int IntSet MakeFset
   SigName arg doesn elt int ll mem namespace sig struct val
   @end[spelling]

   @chapter[modules]{The OCaml Module System}

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

One of the principles of modern programming is @emph{data hiding} using @emph{encapsulation}.  An
@emph{abstract data type} (ADT) is a program unit that defines a data type and functions that
operate on that data type.  In an ADT, the data is @emph{abstract}, meaning that it is not directly
accessible.  Clients that make use of the ADT are required to use the ADT's functions.

There are several ideas behind data hiding using ADTs.  First, by separating a program into distinct
program units (called @emph{modules}), the program may be easier to understand.  Ideally, each
module encapsulates a single concept needed to address the problem at hand.

Second, by hiding the implementation of a program module, dependencies between program modules
become tightly controlled.  Since all interactions must be through a module's functions, the
implementation of the module can be changed without affecting the correctness of the program (as
long as the behavior of functions is preserved).

Finally, the principal motivation of data hiding is that it allows the enforcement of data structure
invariants.  In general, an @emph{invariant} is a property of a data structure that is always true
in a correct program.  Said another way, if the invariant is ever false, then something ``bad'' has
happened and the program has an error.  Invariants are used both for correctness and performance.
For example, balanced binary trees are a frequently-used data structure with the following
invariants 1) each node in the has no more than two children, 2) the nodes are ordered, and 3) the
depth of the tree is logarithmic in the total number of nodes.  The first invariant can be enforced
with the type system (by specifying a type for nodes that allows at most two children), but the
second and third invariants are not so simple to maintain.  When we implement this data structure,
it is more than likely that our implementation will fail if the given a tree that is not properly
ordered (invariant 2).  It may work correctly, though at lower performance, if the tree is not
balanced (invariant 3).

Given the importance of invariants, how can we be sure that they are maintained?  This is where data
hiding comes in.  By restricting the ADT so that only its own functions can directly access the
data, we also limit the amount of reasoning that we have to do.  If each function in the ADT
preserves the invariants, then we can be sure that the invariants are @emph{always} preserved,
because no other part of the program can access the data directly.

Of course, these restrictions can also be awkward.  Often we want partial @emph{transparency} where
some parts of a data structure are abstract but others are directly accessible.  OCaml provides a
general mechanism for data hiding and encapsulation called a @emph{module system}.  An module in
OCaml has two parts: an @emph{implementation} that implements the types, functions, and values in
the module; and a @emph{signature} that specifies which parts of the implementation are publically
accessible.  That is, a signature provides type declarations for the visible parts of the
implementation---everything else is hidden.

------------------------------------------------------------------------

The compilation units discussed in the Chapter @refchapter[files] are not the
only way to create modules.  OCaml provides a general module system
where modules can be created explicitly using the @code{module}
keyword.  There are three key parts in the module system:
@emph{signatures}, @emph{structures}, and @emph{functors}.

Module signatures correspond to the signatures defined in a
@code{.mli} file, and module structures correspond to the
implementations defined in a @code{.ml} file.  There is one major
difference.  Each compilation unit has at most one signature, defined
by the @code{.mli} file.  The module system is more general: a single
signature can be used to specify multiple structures; and a structure
can have multiple signatures.

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

@section["modules-signatures"]{Module signatures}

A module signature is declared with a @code{module type} declaration.

@begin[center]
@tt{module type} @emph{Name} @tt{= sig} @emph{signature} @tt{end}
@end[center]

The name of the signature must begin with an uppercase letter.
The signature can contain any of the items that can occur in an
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

For the finite set example, the signature should include a type
declaration for the set type, and method declarations for the @tt{empty},
@tt{mem}, and @tt{insert} methods.  For this example, we'll return to
the OCaml toploop, which will display the types of the modules we define.

@begin[iverbatim]
# module type FsetSig =
  sig
     type 'a t
     val empty : 'a t
     val mem : 'a -> 'a t -> bool
     val insert : 'a -> 'a t -> 'a t
  end;;
module type FsetSig =
  sig
    type 'a t
    val empty : 'a t
    val mem : 'a -> 'a t -> bool
    val insert : 'a -> 'a t -> 'a t
  end
@end[iverbatim]

The @tt{include} statement can be used to create a new signature that
@emph{extends} an existing signature.  For example, suppose we would
like to define a signature for finite sets that includes a @tt{delete}
function to remove an element of a set.  One way to be to re-type the
entire signature for finite sets followed by the @tt{delete}
declaration.  The @tt{include} statement performs this inclusion
automatically.

@begin[iverbatim]
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
    val insert : 'a -> 'a t -> 'a t
    val delete : 'a -> 'a t -> 'a t
  end
@end[iverbatim]

@section["modules-structures"]{Module structures}

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
in Section @refsubsection["method-definitions"]).

@begin[iverbatim]
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
@end[iverbatim]

@subsection["sig-assignment"]{Assigning a signature}

Note that the default signature assigned to the structure exposes
@emph{all} of the types and functions in the structure, including the
type definitions for the @tt{color} and @code{'a t} types, as well as
the @tt{balance} function, which would normally be hidden.  To assign
a signature to a structure, we include a type constraint using a
@code{:} modifier of the following form.

@begin[center]
@tt{module} @emph{Name} @tt{:} @emph{SigName} @tt{= struct} @emph{implementation} @tt{end}
@end[center]

In the finite set example, we want to assign the @code{FsetSig}
signature to the module.

@begin[iverbatim]
# module Fset : FsetSig =
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
@end[iverbatim]

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
>>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
