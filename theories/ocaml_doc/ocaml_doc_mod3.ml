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

A @emph{functor} is a function over modules; that is, it is a function that computes a module from
one or more others.  Functors offer an expressive power not often seen in other languages, and they
often appear daunting to when first encountered.  However, as we will see, the construction and use
of functors is surprisingly easy.

@section["parameterized-modules"]{Parameterized modules}

One of the simplest appearances of functors is as parameterized modules, where a module is parameterized by another.
The syntax of a parameterized module includes, not surprisingly, a module parameter enclosed in parentheses.

@begin[center]
@bf[module] Name (Arg : @emph{signature}) = @bf[struct] @emph{implementation} @bf[end]
@end[center]

The @emph{Name} is the name of the functor, the parameter @emph{Arg} is a module having the
specified signature, and the @emph{implementation} may refer to the fields of the @emph{Arg} module.

To illustrate the use of a parameterized module, let's return to the set implementation we have been
using in the previous two chapters.  As we noted, the implementation of the set as a list of string
is not very efficient, so as a first step, let's replace it with an implementation using the trees
that were introduced in Chapter @refchapter[unions].  A fragment of the implemention as a module is
shown in Figure @reffigure[rbtree1].

@begin[figure,mset1]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{File: set.ml}}
@hline
@line{{@bf{module type} SetSig = @bf[sig]}}
@line{{$@quad$ @bf[type] 'a t}}
@line{{$@quad$ @bf[val] empty : 'a t}}
@line{{$@quad$ @bf[val] mem : 'a @code{->} 'a t @code{->} bool}}
@line{{$@quad$ @bf[val] add : 'a @code{->} 'a t @code{->} 'a t}}
@line{{@bf[end];;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{}}
@hline
@line{{@bf[module] Set : SetSig = @bf[struct]}}
@line{{$@quad$ @bf[type] 'a t =}}
@line{{$@quad@quad$ | Node @bf[of] 'a @code{*} 'a t @code{*} 'a t}}
@line{{$@quad@quad$ | Leaf}}
@line{{$@quad$ @bf[let] empty = Leaf}}
@line{{$@quad$ @bf[let] mem x = @bf[function]}}
@line{{$@quad@quad$ | Leaf @code{->} false}}
@line{{$@quad@quad$ | Node (y, left, right) @code{->}}}
@line{{$@quad@quad@quad$ x = y}}
@line{{$@quad@quad@quad$ @code{||} (x @code{<} y @code{&&} mem x left)}}
@line{{$@quad@quad@quad$ @code{||} (x @code{>} y @code{&&} mem x right)}}
@line{{$@quad$ @bf[let] add x s = $@cdots$}}
@line{{@bf[end];;}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

One problem with this implementation of finite sets that we have been using is the use of the
built-in @code{<} comparison operation to compare elements in the set.  The definition of the @code{<}
operator is implementation-specific, and it may not always define the exact ordering that we want.

To fix this problem, we should use a custom comparison function @code{compare} that is designed
specifically to compare the elements in the set.  However, this raises a second problem---if the
@code{compare} function is designed for some specific type, it will no longer have a polymorphic
type @code{'a -> 'a -> bool} like the builtin-comparison, it will have some specific type like
@code{int -> int -> bool} or @code{string -> string -> bool}.  When we use the custom @code{compare}
function, the set will no longer be polymorphic, it will be grounded at that type specified by the
@code{compare} function.

To get around this problem, we could potentially copy the code for each set implementation that uses
a different @code{compare} function, but this would be silly.  The alternative is to use functors,
where we compute the @code{Set} module from an argument module @code{Compare} that specifies the
@code{compare} function.  The argument structure includes a type @tt{elt} that specifies the type of
elements in the set, and it includes the comparison function @tt{compare}.  We'll have the
@tt{compare} function return one of three kinds of values:

@begin[itemize]
@item{a @emph{negative} number if the first argument is smaller than the second,}
@item{@emph{zero} if the two arguments are equal,}
@item{a @emph{positive} number if the first argument is larger than the second.}
@end[itemize]

The complete code for the now-parameterized @code{MakeSet} functor is shown in Figure @reffigure[mkset1].
There are several parts to the construction.

@begin[enumerate]

@item{{The @code{CompareSig} signature defines the type of the @code{compare} function for some
specific element type @code{elt}.}}

@item{{Since the @code{compare} function is no longer polymorphic, the @code{SetSig} signature must
also be modified to specifiy some specific type of elements @code{elt}.}}

@item{{The functor, which we now call @code{MakeSet}, takes a @code{Compare} argument structure of
type @code{CompareSig}, and uses the @code{Compare.compare} function instead of using the builtin
comparisons @code{=} and @code{<}.}}

@item{{Since set elements that are equal according to @code{compare} may differ according to @code{=},
we include a @code{find} function, where @code{find x s} returns the actual element in the set that
is equal to @code{x}, or raises @code{Not_found} if no such element exists.  The @code{mem} function
is implemented in terms of @code{find}.}}

@end[enumerate]

@begin[figure,mkset1]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{File: set.ml}}
@hline
@line{{@bf{module type} CompareSig = @bf[sig]}}
@line{{$@quad$ @bf[type] elt}}
@line{{$@quad$ @bf[val] compare : elt @code{->} elt @code{->} int}}
@line{{@bf[end];;}}
@line{{}}
@line{{@bf{module type} SetSig = @bf[sig]}}
@line{{$@quad$ @bf[type] t}}
@line{{$@quad$ @bf[type] elt}}
@line{{$@quad$ @bf[val] empty : t}}
@line{{$@quad$ @bf[val] find : elt @code{->} t @code{->} elt}}
@line{{$@quad$ @bf[val] mem : elt @code{->} t @code{->} bool}}
@line{{$@quad$ @bf[val] add : elt @code{->} t @code{->} t}}
@line{{@bf[end];;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{}}
@hline
@line{{@bf[module] MakeSet (Compare : CompareSig) : SetSig = @bf[struct]}}
@line{{$@quad$ @bf[type] elt = Compare.elt}}
@line{{$@quad$ @bf[type] t =}}
@line{{$@quad@quad$ | Node @bf[of] elt @code{*} t @code{*} t}}
@line{{$@quad@quad$ | Leaf}}
@line{{$@quad$ @bf[let] empty = Leaf}}
@line{{$@quad$ @bf[let] find x = @bf[function]}}
@line{{$@quad@quad$ | Leaf @code{->} @bf[raise] Not_found}}
@line{{$@quad@quad$ | Node (y, left, right) @code{->}}}
@line{{$@quad@quad@quad$ @bf[let] i = Compare.compare x y @bf[in]}}
@line{{$@quad@quad@quad@quad$ @bf[if] i < 0 @bf[then] find x left}}
@line{{$@quad@quad@quad@quad$ @bf{else if} i > 0 @bf[then] find x right}}
@line{{$@quad@quad@quad@quad$ @bf[else] y}}
@line{{$@quad$ @bf[let] mem x s =}}
@line{{$@quad@quad$ @bf[try] ignore (find x s); true @bf[with]}}
@line{{$@quad@quad@quad$ Not_found @code{->} false}}
@line{{$@quad$ @bf[let] add x s = $@cdots$}}
@line{{@bf[end];;}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

@subsection["using-functors"]{Using a functor}

To use the module produced by the functor, we need to @emph{apply} it to a specific structure having
the the @code{CompareSig} signature.  Let's define two different kinds of sets---sets of integers,
and sets of strings, shown in Figure @reffigure[mkset2].

@begin[figure,mkset2]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{@bf[module] CompareInt = @bf[struct]}}
@line{{$@quad$ @bf[type] elt = int}}
@line{{$@quad$ @bf[let] compare i j =}}
@line{{$@quad@quad$ @bf[if] i < j @bf[then] -1}}
@line{{$@quad@quad$ @bf{else if} i > j @bf[then] 1}}
@line{{$@quad@quad$ @bf[else] 0}}
@line{{@bf[end];;}}
@line{{}}
@line{{@bf[module] IntSet = MakeSet (CompareInt);;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{@bf[module] CompareString = @bf[struct]}}
@line{{$@quad$ @bf[type] elt = string}}
@line{{$@quad$ @bf[let] compare s1 s2 =}}
@line{{$@quad@quad$ @bf[if] s1 < s2 @bf[then] -1}}
@line{{$@quad@quad$ @bf{else if} s1 > s2 @bf[then] 1}}
@line{{$@quad@quad$ @bf[else] 0}}
@line{{@bf[end];;}}
@line{{}}
@line{{@bf[module] StringSet = MakeSet (CompareString);;}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

We @emph{must not} give the @code{CompareInt} and @code{CompareString} modules the signature
@tt{CompareSig}.  In the @tt{CompareSig} signature, the @tt{elt} type is abstract.  Since there is
no way to create a value of an abstract type @tt{elt}, it would become impossible to use the
@tt{compare} function, and the modules would become useless.

A functor is applied to an argument with the syntax @tt{@emph{Functor_name} (@emph{Arg_name})}.  To
build a set of integers, we apply the @tt{MakeSet} functor to the @tt{CompareInt} module; and to
build a set of strings we apply the @code{MakeSet} functor to the @code{CompareString} module.

@subsection["sharing-constraints"]{Sharing constraints}

Unfortunately, in the current state, the @tt{IntSet} and @code{StringSet} modules are actually
useless.  Once again, the problem is with type abstraction: the @tt{elt} type is defined as an
@emph{abstract} type in the @tt{SetSig} signature.  The OCaml compiler remembers that the type of
elements @tt{elt} is produced by an application of the functor, but it doesn't know that the types
@code{CompareInt.elt} and @code{IntSet.elt} are both @code{int}.

@begin[iverbatim]
# IntSet.add 5 IntSet.empty;;
Characters 11-12:
This expression has type int but is here used with type
  IntSet.elt = MakeSet(ComapreInt).elt
@end[iverbatim]

To fix this problem, we can't add a type definition in the @tt{SetSig} module, since we want to be
able to construct finite sets with multiple different element types.  The only way to fix this
problem is to add a constraint on the functor type that specifies that the @tt{elt} type produced by
the functor is the @emph{same} as the @tt{elt} type in the argument.

The solution is simple, we can use the @emph{sharing constraints} introduced in Section
@refsection["sharing-constraints"].  The corrected definition of the @tt{MakeSet} functor uses a sharing constraint to specify that the @code{elt} types of the argument and result modules are the same.

@begin[center]
@begin[tabular,l]
@line{{@bf[module] MakeSet (Compare : CompareSig)}}
@line{{$@quad$ : SetSig @bf{with type} elt = Compare.elt}}
@line{{$@quad$ = @bf[struct] $@cdots$ @bf[end];;}}
@end[tabular]
@end[center]

The toploop now displays the correct element specification.  When we redefine the @tt{IntSet}
module, we get a working version of finite sets of integers.

@begin[iverbatim]
# module IntSet = MakeFset (Int);;
module IntSet :
  sig
    type elt = Int.elt
    and t = MakeFset(Int).t
    val empty : t
    val mem : elt -> t -> bool
    val add : elt -> t -> t
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

@section["module-reuse"]{Module re-use using functors}

One might wonder about the premise of the previous section.  Why should we want to use a special
@code{compare} function when the builtin @code{<} comparison seems perfectly adequate?

One reason, which we illustrate in this section, is that the implementation is now more flexible and
can be used for other purposes.  Another frequently-used data structure, called a @emph{map}, is a
table that associates a value with each element in a set.  The data structure provides a function
@code{add} to add an element and its value to the table, as well as a function @code{find} that
retrieves that value associated with an element (or raises the exception @code{Not_found} if the
element is not in the table).

The @emph{map} and @emph{set} data structures are very similar.  Since we have implemented sets
already, is it possible to re-use the implementation for maps.  Once again, we can use functors for
this purpose.  In this case, we will write a functor that produces a @emph{map} data structure given
a comparison function.  The code is shown in Figure @reffigure[mkset3].

@begin[figure,mkset3]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{@bf{module type} ValueSig = @bf[sig]}}
@line{{$@quad$ @bf[type] value}}
@line{{@bf[end];;}}
@line{{}}
@line{{@bf{module type} MapSig = @bf[sig]}}
@line{{$@quad$ @bf[type] t}}
@line{{$@quad$ @bf[type] key}}
@line{{$@quad$ @bf[type] value}}
@line{{$@quad$ @bf[val] empty : t}}
@line{{$@quad$ @bf[val] add : t @code{->} key @code{->} value @code{->} t}}
@line{{$@quad$ @bf[val] find : t @code{->} key @code{->} value}}
@line{{@bf[end];;}}
@line{{}}
@line{{A @code{string -> int} map}}
@hline
@line{{@bf[module] IntValue = @bf[struct]}}
@line{{$@quad$ @bf[type] value = int}}
@line{{@bf[end];;}}
@line{{@bf[module] StringIntTable =}}
@line{{$@quad$ MakeMap (CompareString) (IntValue);;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{@bf[module] MakeMap (Compare : CompareSig) (Value : ValueSig)}}
@line{{$@quad$ : MapSig}}
@line{{$@quad@quad$ @bf{with type} key = Compare.elt}}
@line{{$@quad@quad$ @bf{with type} value = Value.value}}
@line{{= @bf[struct]}}
@line{{$@quad$ @bf[type] key = Compare.elt}}
@line{{$@quad$ @bf[type] value = Value.value}}
@line{{$@quad$ @bf[module] CompareKey = @bf[struct]}}
@line{{$@quad@quad$ @bf[type] elt = key * value}}
@line{{$@quad@quad$ @bf[let] compare (key1, _) (key2, _) =}}
@line{{$@quad@quad@quad$ Compare.compare key1 key2}}
@line{{$@quad$ @bf[end];;}}
@line{{$@quad$ @bf[module] Set = MakeSet (CompareKey);;}}
@line{{$@quad$ @bf[type] t = Set.t}}
@line{{$@quad$ @bf[let] empty = Set.empty}}
@line{{$@quad$ @bf[let] add map key value = Set.add (key, value) map}}
@line{{$@quad$ @bf[let] find map key = snd (Set.find map key)}}
@line{{@bf[end];;}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

The @code{MakeMap} functor takes two parameters, a @code{Compare} module to compare keys, and a
@code{Value} module that specifies the type of values stored in the table.  The functor itself first
constructs a @code{Set} module for @code{(key, value)} pairs, where the comparison is limited to the
keys.  Once the @code{Set} module is constructed, the @code{Map} functions are simple wrappers
around the @code{Set} functions.

@section["higher-order-functors"]{Higher-order functors}

A @emph{higher-order} functor is a functor that takes a functor as an argument.  While higher-order
functors are rarely used in practice, there are times when they can be useful.

For example, in relation to our running example, the @code{MakeMap} functor is tied to a specific
definition of the @code{MakeSet} functor.  If we have multiple ways to build sets (for example, as
lists, trees, or some other data structure), we may want to be able to use any of these sets when
building a map.  The solution is to pass the @code{MakeSet} functor as a parameter to @code{MakeMap}.

The type of a functor is specified using the @bf[functor] keyword, where $@it{signature}_2$ is
allowed to depend on the argument @code{Arg}.

@begin[center]
@bf[functor] (Arg : $@it{signature}_1$) @code{->} $@it{signature}_2$
@end[center]

When passing the @code{MakeSet} functor to @code{MakeMap}, we need to specify the functor type with
its sharing constraint.  The @code{MakeMap} definition changes as follows; the structure definition
itself doesn't change.

@begin[center]
@begin[tabular,l]
@line{{@bf[module] MakeMap (Compare : CompareSig) (Value : ValueSig)}}
@line{{$@quad$ (MakeSet : @bf[functor] (CompareElt : CompareSig) @code{->}}}
@line{{$@quad@quad$ SetSig @bf{with type} elt = CompareElt.elt)}}
@line{{$@quad$ : MapSig}}
@line{{$@quad@quad$ @bf{with type} key = Compare.elt}}
@line{{$@quad@quad$ @bf{with type} value = Value.value}}
@line{{= @bf[struct] $@cdots$ @bf[end]}}
@end[tabular]
@end[center]

These types can get complicated!  Certainly, it can get even more complicated with the ability to
specify a functor argument that itself takes a functor.  However, as we mentioned, higher-order
functors are used fairly infrequently in practice, partly because they can be hard to understand.
In general, it is wise to avoid gratuitious use of higher-order functors.

@section["to-do"]{TODO}

@begin[itemize]
@item{{Recursive modules}}
@item{{Module sharing constraints}}
@end[itemize]

@docoff

>>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
