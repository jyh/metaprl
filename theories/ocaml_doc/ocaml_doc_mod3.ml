(* -*- Mode: text; fill-column: 100 -*- *)
doc <:doc<

   @begin[spelling]
   Arg ArgName ArgSig Elt EltSig FsetSig Int IntSet MakeFset
   SigName arg elt int ll mem namespace sig struct val
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

Modules often refer to other modules.  The modules we saw in Chapter @refchapter[modules] referred
to other modules by name.  Thus, all the module references we've seen up to this point have been to
specific, constant modules.

It's also possible in OCaml to write modules that take one or more module parameters.  These
parameterized modules, called @emph{functors}, might be thought of as ``module skeletons.''  To be
used, functors are instantiated by supplying actual module arguments for the functor's module
parameters (similar to supplying arguments in a function call).

To illustrate the use of a parameterized module, let's return to the set implementation we have been
using in the previous two chapters.  One of the problems with that implementation is that the
elements are compared using the OCaml built-in equality function @code{=}.  For example, we might
want a set of strings where equality is case-insensitive, or we might want a set of floating-point
numbers where equality is to within a small constant.  Rather than re-implementing a new set for
each of these cases, we can implement it as a functor, where the equality function is provided as a
parameter.  An example is shown inf Figure @reffigure[mset1].

@begin[figure,mset1]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{Set functor}}
@hline
@line{{@bf{module type} EqualSig = @bf[sig]}}
@line{{$@quad$ @bf[type] t}}
@line{{$@quad$ @bf[val] equal : t @code{->} t @code{->} bool}}
@line{{@bf[end];;}}
@line{{}}
@line{{@bf[module] MakeSet (Equal : EqualSig) =}}
@line{{@bf[struct]}}
@line{{$@quad$ @bf[open] Equal}}
@line{{$@quad$ @bf[type] elt = Equal.elt}}
@line{{$@quad$ @bf[type] t = elt list}}
@line{{$@quad$ @bf[let] empty = []}}
@line{{$@quad$ @bf{let rec} mem x = @bf[function]}}
@line{{$@quad @quad$ | x' :: l @code{->} equal x x' || mem x l}}
@line{{$@quad @quad$ | [] @code{->} false}}
@line{{$@quad$ @bf[let] add x l = x :: l}}
@line{{$@quad$ @bf{let rec} find x = @bf[function]}}
@line{{$@quad @quad$ | x' :: l @bf[when] equal x x' @code{->} x'}}
@line{{$@quad @quad$ | _ :: l @code{->} find x l}}
@line{{$@quad @quad$ | [] @code{->} @bf[raise] Not_found}}
@line{{@bf[end];;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Building a specific set}}
@hline
@line{{@bf{module} StringCaseEqual = @bf[struct]}}
@line{{$@quad$ @bf[type] t = string}}
@line{{$@quad$ @bf[let] equal s1 s2 =}}
@line{{$@quad @quad$ String.lowercase s1 = String.lowercase s2}}
@line{{@bf[end];;}}
@line{{@bf[module] SSet = MakeSet (StringCaseEqual);;}}
@line{{}}
@line{{Using the set}}
@hline
@line{{@code{#} @bf[let] s = SSet.add @code{"}Great Expectations@code{"} SSet.empty;;}}
@line{{@bf[val] s : string list = [@code{"}Great Expectations@code{"}]}}
@line{{@code{#} SSet.mem @code{"}great eXpectations@code{"} s;;}}
@line{{- : bool = true}}
@line{{@code{#} SSet.find @code{"}great eXpectations@code{"} s;;}}
@line{{- StringCaseEqual.t = @code{"}Great Expectations@code{"}}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

In this example, the module @code{MakeSet} is a functor that takes another module @code{Equal} with
signature @code{EqualSig} as an argument.  The @code{Equal} module provides two things---a type of
elements, and a function @code{equal} to compare two elements.  The body of the functor
@code{MakeSet} is much the same as the previous set implementations we have seen, except now the
elements are compared using the function @code{equal x x'} instead of the builtin-equality @code{x =
x'}.

To construct a specific set, we first build a module that implements the equality function (in this
case, the module @code{StringCaseEqual}), then apply the @code{MakeSet} functor module to construct
the set module.

In many ways, functors are just like functions at the module level, and they can be used just like
functions.  However, there are a few things to keep in mind.

@begin[enumerate]

@item{{A functor parameter, like @code{(Equal : EqualSig)} must be a module, or another functor.  It
is not legal to pass non-module values (like strings, lists, or integers).}}

@item{{Syntactically, module and functor identifiers must always be capitalized.  Functor
parameters, like @code{(Equal : EqualSig)}, must be enclosed in parentheses, and the signature is
required.  For functor applications, like @code{MakeSet (StringCaseEqual)}, the argument must be
enclosed in parenthesis.}}

@item{{Modules and functors are not first class.  That is, they can't be stored in data structures
or passed as arguments like other values, and module definitions cannot occur in function bodies.
Technically speaking, the primary reason for this restriction is that type checking would become
undecidable.  Another reason is that module constructions and functor applications are normally
computed at compile time, so it would not be legal to have a function compute a module.}}

@end[enumerate]

Another point to keep in mind is that the new set implementation is no longer polymorphic---it is
now defined for a specific type of elements defined by the @code{Equal} module.  This loss of
polymorphism occurs frequently when modules are parameterized, because the goal of parameterizing is
to define different behaviors for different types of elements.  While the loss of polymorphism is
inconvenient, in practice, it is rarely an issue because modules can be constructed for each
specific type of parameter by using a functor application.

@section["sharing-constraints"]{Sharing constraints}

In the @code{MakeSet} example of Figure @reffigure[mset1], we omitted the signature for sets.  This
leaves the set implementation visible (for example, the @code{SSet.add} function returns a string
list).  As usual, it would be wise define a signature that hides the implementation, preventing the
rest of the program from depending on the implementation details.

Functor signatures are defined the usual way, by specifying the signature after a colon, as shown in
Figure @reffigure[mset2].

@begin[figure,mset1]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{Set functor}}
@hline
@line{{@bf{module type} EqualSig = @bf[sig]}}
@line{{$@quad$ @bf[type] t}}
@line{{$@quad$ @bf[val] equal : t @code{->} t @code{->} bool}}
@line{{@bf[end];;}}
@line{{}}
@line{{@bf{module type} SetSig = @bf[sig]}}
@line{{$@quad$ @bf[type] t}}
@line{{$@quad$ @bf[type] elt}}
@line{{$@quad$ @bf[val] empty : t}}
@line{{$@quad$ @bf[val] mem : elt @code{->} t @code{->} bool}}
@line{{$@quad$ @bf[val] add : elt @code{->} t @code{->} t}}
@line{{$@quad$ @bf[val] find : elt @code{->} t @code{->} elt}}
@line{{@bf[end];;}}
@line{{}}
@line{{@bf[module] MakeSet (Equal : EqualSig) : SetSig =}}
@line{{@bf[struct]}}
@line{{$@quad$ @bf[type] elt = Equal.elt}}
@line{{$@quad$ @bf[type] t = elt list}}
@line{{$@quad$ @bf[let] empty = []}}
@line{{$@quad @cdots$}}
@line{{@bf[end];;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Building a specific set}}
@hline
@line{{@bf{module} StringCaseEqual = @bf[struct]}}
@line{{$@quad$ @bf[type] t = string}}
@line{{$@quad$ @bf[let] equal s1 s2 =}}
@line{{$@quad @quad$ String.lowercase s1 = String.lowercase s2}}
@line{{@bf[end];;}}
@line{{@bf[module] SSet = MakeSet (StringCaseEqual);;}}
@line{{}}
@line{{Using the set}}
@hline
@line{{@code{#} SSet.empty;;}}
@line{{- : StringSet.t = @code{<abstr>}}}
@line{{@code{#} @bf[let] s = SSet.add @underline{"Great Expectations"} SSet.empty;;}}
@line{{This expression has type string}}
@line{{$@quad$ but is here used with type}}
@line{{$@quad$ StringSet.elt = MakeSet(StringCaseEqual).elt}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

Unfortunately, in this attempt, the @code{SSet} module is actually useless because of type
abstraction.  In the @code{SetSig} signature, the type @tt{elt} is abstract, and since the
@code{MakeSet} functor returns a module with signature @code{SetSig}, the type @code{SSet.elt} is
also abstract.  While we know that the type @code{SSet.elt} is really @code{string}, we can't make
use of the fact.

One solution might be to define a transparent type @code{type elt = string} in the @code{SetSig}
module, but this would mean that we could only construct sets of strings.  Instead, the proper way
to fix the problem is to add a constraint on the functor that specifies that the @tt{elt} type
produced by the functor is the @emph{same} as the @tt{Equal.elt} type in the argument.

The solution is simpleTo do this, we can use the @emph{sharing constraints} introduced in Section
@refsection["sharing-constraints"].  The corrected definition of the @tt{MakeSet} functor uses a
sharing constraint to specify that the @code{elt} types of the argument and result modules are the
same.

@begin[center]
@begin[tabular,l]
@line{{@bf[module] MakeSet (Equal : EqualSig)}}
@line{{$@quad$ : SetSig @bf{with type} elt = Equal.t}}
@line{{$@quad$ = @bf[struct] $@cdots$ @bf[end];;}}
@end[tabular]
@end[center]

The toploop now displays the correct element specification.  When we redefine the @tt{SSet}
module, we get a working version of finite sets of integers.

@begin[iverbatim]
# module SSet = MakeSet (StringCaseCompare);;
module SSet :
  sig
    type elt = StringCaseCompare.t
    and t = MakeSet(Int).t
    val empty : t
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val find : elt -> t -> elt
  end
# SSet.empty;;
- : IntSet.t = <abstr>
# open SSet;;
# let s = add "Great Expectations" empty;;
val s : SSet.t = <abstr>
# mem "great eXpectations" s;;
- : bool = true
# find "great eXpectations" s;;
- : string = "Great Expectations"
@end[iverbatim]

@section["module-reuse"]{Module re-use using functors}

Now that we have successfully constructed the @code{MakeSet} functor, let's move on to another
frequently-used data structure called a @emph{map}.  A map is a table that associates a value with
each element in a set.  The data structure provides a function @code{add} to add an element and its
value to the table, as well as a function @code{find} that retrieves that value associated with an
element (or raises the exception @code{Not_found} if the element is not in the table).

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
@line{{A (string, int) map}}
@hline
@line{{@bf[module] IntValue = @bf[struct]}}
@line{{$@quad$ @bf[type] value = int}}
@line{{@bf[end];;}}
@line{{@bf[module] StringIntTable =}}
@line{{$@quad$ MakeMap (EqualString) (IntValue);;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{@bf[module] MakeMap (Equal : EqualSig) (Value : ValueSig)}}
@line{{$@quad$ : MapSig}}
@line{{$@quad@quad$ @bf{with type} key = Equal.t}}
@line{{$@quad@quad$ @bf{with type} value = Value.value}}
@line{{= @bf[struct]}}
@line{{$@quad$ @bf[type] key = Equal.t}}
@line{{$@quad$ @bf[type] value = Value.value}}
@line{{$@quad$ @bf[module] EqualKey = @bf[struct]}}
@line{{$@quad@quad$ @bf[type] t = key * value}}
@line{{$@quad@quad$ @bf[let] equal (key1, _) (key2, _) =}}
@line{{$@quad@quad@quad$ Equal.equal key1 key2}}
@line{{$@quad$ @bf[end];;}}
@line{{$@quad$ @bf[module] Set = MakeSet (EqualKey);;}}
@line{{$@quad$ @bf[type] t = Set.t}}
@line{{$@quad$ @bf[let] empty = Set.empty}}
@line{{$@quad$ @bf[let] add map key value = Set.add (key, value) map}}
@line{{$@quad$ @bf[let] find map key = snd (Set.find map key)}}
@line{{@bf[end];;}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

The @code{MakeMap} functor takes two parameters, a @code{Equal} module to compare keys, and a
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
