(* -*- Mode: text; fill-column: 100 -*- *)
doc <:doc<

   @begin[spelling]
   Arg ArgName ArgSig Elt EltSig FsetSig Int IntSet MakeFset
   SigName arg elt int ll mem namespace sig struct val
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

As we saw in the previous chapter, programs can be divided into parts that can be implemented in
files, and each file can be given an interface that specifies what its public types and values are.
Files are not the only way to partition a program, OCaml also provides a @emph{module system} that
allows programs to be partitioned even within a single file.  There are three key parts in the
module system: @emph{signatures}, @emph{structures}, and @emph{functors}, where signatures
correspond to interfaces, structures correspond to implementations, and functors are functions over
structures.  In this chapter, we will discuss the first two; we'll leave discussion of functors in
Chapter @refchapter[functors].

There are several reasons for using the module system.  Perhaps the simplest reason is that each
structure has its own namespace, so name conflicts are less likely when modules are used.  Another
reason is that abstraction can be specified explicitly by assigning a signature to a structure.
To begin, let's return to the @code{unique} example from the previous chapter, this time using modules
instead of separate files.

@section["simple-modules"]{Simple modules}

Named structures are defined with the @tt{module} and @tt{struct} keywords using the following syntax.

@begin[center]
@tt{module} @emph{Name} @tt{= struct} @emph{implementation} @tt{end}
@end[center]

The module @emph{Name} must begin with an uppercase letter.  The @emph{implementation} can include
definition that might occur in a @code{.ml} file.  Let's return to the @code{unique.ml} example from
the previous chapter, using a simple list-based implementation of sets.  This time, instead of
defining the set data structure in a separate file, let's define it as a module, called @code{Set},
using an explicit @code{module/struct} definition.  The program is shown in Figure
@reffigure[mset1].

@begin[figure,mset1]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{File: unique.ml}}
@hline
@line{{@bf[module] Set = @bf[struct]}}
@line{{$@quad$ @bf[let] empty = []}}
@line{{$@quad$ @bf[let] add x l = x @code{::} l}}
@line{{$@quad$ @bf[let] mem x l = List.mem x l}}
@line{{@bf[end];;}}
@line{{}}
@line{{@bf[let] @bf[rec] unique already_read =}}
@line{{$@quad$ output_string stdout @code{"> ";}}}
@line{{$@quad$ flush stdout;}}
@line{{$@quad$ @bf[let] line = input_line stdin @bf[in]}}
@line{{$@quad @quad$ @bf[if] not (Set.mem line already_read) @bf{then begin}}}
@line{{$@quad @quad @quad$ output_string stdout line;}}
@line{{$@quad @quad @quad$ output_char stdout @code{'\n'};}}
@line{{$@quad @quad @quad$ uniq (Set.add line already_read)}}
@line{{$@quad @quad$ @bf[end] @bf[else]}}
@line{{$@quad @quad @quad$ unique already_read;;}}
@line{{}}
@line{{@it{{(}{*} Main program {*}{)}}}}
@line{{@bf[try] unique Set.empty @bf[with]}}
@line{{$@quad$ End_of_file ->}}
@line{{$@quad @quad$ ();;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Example run}}
@hline
@line{{@code{%} ocamlc -o unique unique.ml}}
@line{{@code{%} ./unique}}
@line{{@code{>} Adam Bede}}
@line{{Adam Bede}}
@line{{@code{>} A Passage to India}}
@line{{A Passage to India}}
@line{{@code{>} Adam Bede}}
@line{{@code{>} Moby Dick}}
@line{{Moby Dick}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

In this new program, the main role of the module @code{Set} is to collect the set functions into a
single block of code that has an explicit name.  The values are now named using the module name as a
prefix as @code{Set.empty}, @code{Set.add}, and @code{Set.mem}.  Otherwise, the program is as
before.

One problem with this program is that the implementation of the @code{Set} module is visible.  As
usual, we would like to hide the type of set, making it easier to replace the implementation later
if we wish to improve its performance.  To do this, we can assign an explicit signature that hides
the set implementation.  A named signature is defined with a @code{module type} definition.

@begin[center]
@tt{module type} @emph{Name} @tt{= sig} @emph{signature} @tt{end}
@end[center]

As before, the name of the signature must begin with an uppercase letter.  The signature can contain
any of the items that can occur in an interface @code{.mli} file.  For our example, the signature
should include an abstract type declaration for the @code{'a set} type and @code{val} declarations
for each of the values.  The @code{Set} module's signature is constrained by specifying the
signature after a colon in the module definition @bf[module] Set : SetSig = @bf[struct] $@cdots$
@bf[end], as shown in Figure @reffigure[mset2].

@begin[figure,mset2]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{Signature definition}}
@hline
@line{{@bf{module type} SetSig = @bf[sig]}}
@line{{$@quad$ @bf[type] 'a set}}
@line{{$@quad$ @bf[val] empty : 'a set}}
@line{{$@quad$ @bf[val] add : 'a @code{->} 'a set @code{->} 'a set}}
@line{{$@quad$ @bf[val] mem : 'a @code{->} 'a set @code{->} bool}}
@line{{@bf[end];;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Structure definition}}
@hline
@line{{@bf[module] Set : SetSig = @bf[struct]}}
@line{{$@quad$ @bf[type] 'a set = 'a list}}
@line{{$@quad$ @bf[let] empty = []}}
@line{{$@quad$ @bf[let] add x l = x @code{::} l}}
@line{{$@quad$ @bf[let] mem x l = List.mem x l}}
@line{{@bf[end];;}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

@section["module-contents"]{Module definitions}

In general, structures and signatures are just like implementation files and their interfaces.
Structures are allowed to contain any of the definitions that might occur in a implementation,
including any of the following.

@begin[itemize]
@item{@tt{type} definitions}
@item{@tt{exception} definitions}
@item{@tt{let} definitions}
@item{@tt{open} statements to open the namespace of another module}
@item{@tt{include} statements that include the contents of another module}
@item{signature definitions}
@item{nested structure definitions}
@end[itemize]

Similarly, signatures may contain any of the declarations that might occur in an interface file,
including any of the following.

@begin[itemize]
@item{@tt{type} declarations}
@item{@tt{exception} definitions}
@item{@tt{val} declarations}
@item{@tt{open} statements to open the namespace of another signature}
@item{@tt{include} statements that include the contents of another signature}
@item{nested signature declarations}
@end[itemize]

We have seen most of these constructs before.  However, one new construct we haven't seen is
@code{include}, which allows the entire contents of a structure or signature to be included in
another.  The @tt{include} statement can be used to create modules and signatures that re-use
existing definitions.

@subsection[include]{Using include to extend modules}

Suppose we wish to defined a new kind of sets @code{ChooseSet} that have a @code{choose} function
that returns an element of the set if one exists.  Instead of re-typing the entire signature, we can
use the @code{include} statement to include the existing signature, as shown in Figure
@reffigure[mset3].  The resulting signature includes all of the types and declarations from
@code{SetSig} as well as the new (transparent) type definition @code{'a choice} and function
declaration @code{val choose}.  For this example, we are using the toploop to display the infered
signature for the new module.

@begin[figure,mset3]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{Signature definition}}
@hline
@line{{@bf{module type} ChooseSetSig = @bf[sig]}}
@line{{$@quad$ @bf[include] SetSig}}
@line{{$@quad$ @bf[type] 'a choice = Element of 'a | Empty}}
@line{{$@quad$ @bf[val] choose : 'a set @code{->} 'a choice}}
@line{{@bf[end];;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Inferred type (from the toploop)}}
@hline
@line{{@bf{module type} ChooseSetSig = @bf[sig]}}
@line{{$@quad$ @bf[type] 'a set}}
@line{{$@quad$ @bf[val] empty : 'a set}}
@line{{$@quad$ @bf[val] add : 'a @code{->} 'a set @code{->} 'a set}}
@line{{$@quad$ @bf[val] mem : 'a @code{->} 'a set @code{->} bool}}
@line{{$@quad$ @bf[type] 'a choice = Element of 'a | Empty}}
@line{{$@quad$ @bf[val] choose : 'a set @code{->} 'a choice}}
@line{{@bf[end];;}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

@subsection["include-struct"]{Using include to extend implementations}

The @tt{include} statement can also be used in implementations.  For our example, however, there is
a problem.  The straightforward approach in defining a module @code{ChooseSet} is to include the
@code{Set} module, then define the new type @code{'a choice} and the new function @code{choose}.
The result of this attempt is shown in Figure @reffigure[mset4], where the toploop prints out an
extensive error message (the toploop prints out the full signature, which we have elided in @bf[sig]
$@cdots$ @bf[end]).

@begin[figure,mset4]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{Module definition}}
@hline
@line{{@bf{module} ChooseSet : ChooseSetSig = @bf[struct]}}
@line{{$@quad$ @bf[include] Set}}
@line{{$@quad$ @bf[type] 'a choice = Element of 'a | Empty}}
@line{{$@quad$ @bf[let] choose = @bf[function]}}
@line{{$@quad @quad$ | x :: _ @code{->} Element x}}
@line{{$@quad @quad$ | [] @code{->} Empty}}
@line{{@bf[end];;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Inferred type (from the toploop)}}
@hline
@line{{Signature mismatch:}}
@line{{Modules do not match:}}
@line{{$@quad$ @bf[sig] $@cdots$ @bf[end]}}
@line{{is not included in}}
@line{{$@quad$ ChooseSetSig}}
@line{{Values do not match:}}
@line{{$@quad$ @bf[val] choose : 'a list @code{->} 'a choice}}
@line{{is not included in:}}
@line{{$@quad$ @bf[val] choose : 'a set @code{->} 'a choice}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

The problem is apparent from the last few lines of the error message---the @code{choose} function
has type @code{'a list -> 'a choice}, not @code{'a set -> 'a choice} as it should.  The issue is
that we included the @emph{abstract} module @code{Set}, where the type @code{'a set} is an abstract
type, not a list.

One solution is to manually copy the code from the @code{Set} module into the @code{ChooseSet}
module.  This has its drawbacks of course.  We aren't able to re-use the existing implementation,
our code base gets larger, etc.  If we have access to the original non-abstract set implementation,
there is another solution--we can just include the non-abstract set implementation, where it is
known that the set is represented as a list.

Suppose we start with a non-abstract implementation @code{SetInternal} of sets as lists.  Then the
module @code{Set} is the same implementation, with the signature @code{SetSig}; and the
@code{ChooseSet} includes the @code{SetInternal} module instead of @code{Set}.  Figure
@reffigure[mset5] shows the definitions in this order, together with the types inferred by the
toploop.

@begin[figure,mset5]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{Module definitions}}
@hline
@line{{@bf[module] SetInternal = @bf[struct]}}
@line{{$@quad$ @bf[type] 'a set = 'a list}}
@line{{$@quad$ @bf[let] empty = []}}
@line{{$@quad$ @bf[let] add x l = x :: l}}
@line{{$@quad$ @bf[let] mem x l = List.mem x l}}
@line{{@bf[end];;}}
@line{{}}
@line{{@bf[module] Set : SetSig = SetInternal}}
@line{{}}
@line{{@bf{module} ChooseSet : ChooseSetSig = @bf[struct]}}
@line{{$@quad$ @bf[include] SetInternal}}
@line{{$@quad$ @bf[type] 'a choice = Element of 'a | Empty}}
@line{{$@quad$ @bf[let] choose = @bf[function]}}
@line{{$@quad @quad$ | x :: _ @code{->} Element x}}
@line{{$@quad @quad$ | [] @code{->} Empty}}
@line{{@bf[end];;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Inferred types (from the toploop)}}
@hline
@line{{@bf[module] SetInternal : @bf[sig]}}
@line{{$@quad$ @bf[type] 'a set = 'a list}}
@line{{$@quad$ @bf[val] empty : 'a list}}
@line{{$@quad$ @bf[val] add : 'a @code{->} 'a list @code{->} 'a list}}
@line{{$@quad$ @bf[val] mem : 'a @code{->} 'a list @code{->} bool}}
@line{{@bf[end];;}}
@line{{}}
@line{{@bf[module] Set : SetSig}}
@line{{}}
@line{{@bf[module] ChooseSet : ChooseSetSig}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

Note that for the module @code{Set} it is not necessary to use a @bf[struct] $@cdots$ @bf[end]
definition because the @code{Set} module is @emph{equivalent} to the @code{SetInternal} module, it
just has a different signature.  The modules @code{Set} and @code{ChooseSet} are ``friends,'' in
that they share internal knowledge of each other's implementation, while keeping their public
signatures abstract.

@section["module-hiding"]{Abstraction, friends, and module hiding}

So far, we have seen that modules provide two main features, 1) the ability to divide a program into
separate program units (modules) that each have a separate namespace, and 2) the ability to assign
signatures that make each structure partially or totally abstract.  In addition, as we have seen in
the previous example, a structure like @code{SetInternal} can be given more than one signature (the
module @code{Set} is equal to @code{SetInternal} but it has a different signature).

Another frequent use of modules uses nesting to define multiple levels of abstraction.  For example,
we might define a module container in which several modules are defined and implementation are
visible, but the container type is abstract.  This is akin to the C++ notion of ``friend'' classes,
where a set of friend classes may mutually refer to class implementations, but the publicly visible
fields remain protected.

In our example, there isn't much danger in leaving the @code{SetInternal} module publicly
accessible.  A @code{SetInternal.set} can't be used in place of a @code{Set.set} or a
@code{ChooseSet.set}, because the latter types are abstract.  However, there is a cleaner solution
that nests the @code{Set} and @code{ChooseSet} structures in an outer @code{Sets} module.  The
signatures are left unconstrained within the @code{Sets} module, allowing the @code{ChooseSet}
structure to refer to the implementation of the @code{Set} structure, but the signature of the
@code{Sets} module is constrained.  The code for this is shown in Figure@reffigure[mset6].

@begin[figure,mset6]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{Module definitions}}
@hline
@line{{@bf[module] Sets : @bf[sig]}}
@line{{$@quad$ @bf[module] Set : SetSig}}
@line{{$@quad$ @bf[module] ChooseSet : ChooseSetSig}}
@line{{@bf[end] = @bf[struct]}}
@line{{$@quad$ @bf[module] Set = @bf[struct]}}
@line{{$@quad @quad$ @bf[type] 'a set = 'a list}}
@line{{$@quad @quad$ @bf[let] empty = []}}
@line{{$@quad @quad$ @bf[let] add x l = x :: l}}
@line{{$@quad @quad$ @bf[let] mem x l = List.mem x l}}
@line{{$@quad$ @bf[end]}}
@line{{$@quad$ @bf{module} ChooseSet = @bf[struct]}}
@line{{$@quad @quad$ @bf[include] Set}}
@line{{$@quad @quad$ @bf[type] 'a choice = Element of 'a | Empty}}
@line{{$@quad @quad$ @bf[let] choose = @bf[function]}}
@line{{$@quad @quad @quad$ | x :: _ @code{->} Element x}}
@line{{$@quad @quad @quad$ | [] @code{->} Empty}}
@line{{$@quad$ @bf[end]}}
@line{{@bf[end];;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Inferred types (from the toploop)}}
@hline
@line{{@bf[module] Sets : @bf[sig]}}
@line{{$@quad$ @bf[module] Set : SetSig}}
@line{{$@quad$ @bf[module] ChooseSet : ChooseSetSig}}
@line{{@bf[end]}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

There are a few things to note of this definition.
@begin[enumerate]

@item{{The @code{Sets} module uses an @emph{anonymous} signature (meaning that the signature has no
name).  Anonymous signatures and @bf[struct] implementations are perfectly acceptable any place
where a signature or structure is needed.}}

@item{{Within the @code{Sets} module the @code{Set} and @code{ChooseSet} modules are not
constrained, so that their implementations are public.  This allows the @code{ChooseSet} to refer to
the @code{Set} implementation directly (so in this case, the @code{Set} and @code{ChooseSet} modules
are firends).  The signature for the @code{Sets} module makes them abstract.}}

@end[enumerate]

@subsection["incompatible-include"]{Using include with incompatible signatures}

In our current example, it might seem that there isn't much need to have two separate modules
@code{ChooseSet} (with @code{choice}) and @code{Set} (without @code{choice}).  In practice it is
perhaps more likely that we would simply add a @code{choice} function to the @code{Set} module.  The
addition would not affect any existing code, since any existing code doesn't refer to the
@code{choice} function anyway.

Surprisingly, this kind of example occurs in practice more than it might seem, due to programs being
developed with incompatible signatures.  For example, suppose we are writing a program that is going
to make use of two independently-developed libraries.  Both libraries have their own @code{Set}
implementation, and we decide that we would like to use a single @code{Set} implementation in the
combined program.  Unfortunately, the signatures are incompatible---in the first library, the
@code{add} function was defined with type @code{val add : 'a -> 'a set -> 'a set}; but in the second
library, it was defined with type @code{val add : 'a set -> 'a -> 'a set}.  Let's say that the first
library uses the desired signature.  Then, one solution would be to hunt through the second library,
finding all calls to the @code{Set.add} function, reordering the arguments to fit a common
signature.  Of course, the process is tedious, and it is unlikely we would want to do it.

An alternative is to @emph{derive} a wrapper module @code{Set2} for use in the second library.  The
process is simple, 1) @code{include} the @code{Set} module, and 2) redefine the @code{add} to match
the desired signature; this is shown in Figure @reffigure[mset7].

@begin[figure,mset7]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{Signature}}
@hline
@line{{@bf{module type} Set2Sig = @bf[sig]}}
@line{{$@quad$ @bf[type] 'a set}}
@line{{$@quad$ @bf[val] empty : 'a set}}
@line{{$@quad$ @bf[val] add : 'a set @code{->} 'a @code{->} 'a set}}
@line{{$@quad$ @bf[val] mem : 'a @code{->} 'a set @code{->} bool}}
@line{{@bf[end]}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Implementation}}
@hline
@line{{@bf[module] Set2 : Set2Sig = @bf[struct]}}
@line{{$@quad$ @bf[include] Set}}
@line{{$@quad$ @bf[let] add l x = Set.add x l}}
@line{{@bf[end];;}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

The @code{Set2} module is just a wrapper.  Apart from the @code{add} function, the types and values
in the @code{Set} and @code{Set2} modules are the same, and the @code{Set2.add} function simply
reorders the arguments before calling the @code{Set.add} function.  There is little or no
performance penalty for the wrapper---in most cases the native-code OCaml compiler will
@emph{inline} the @code{Set2.add} function (in other words, it will perform the argument reordering
at compile time).

@section["sharing-constraints"]{Sharing constraints}

There is one remaining problem with this example.  In the combined program, the first library uses
the original @code{Set} module, and the second library uses @code{Set2}.  It is likely that we will
want to pass values, including sets, from one library to the other.  However, as defined, the
@code{'a Set.set} and @code{'a Set2.set} types are distinct abstract types, and it is an error to
use a value of type @code{'a Set.set} in a place where a value of type @code{'a Set2.set} is
expected, and @emph{vice-versa}.  The following error message is typical.

@begin[iverbatim]
# Set2.add Set.empty 1;;
This expression has type 'a Set.set
   but is here used with type 'b Set2.set
@end[iverbatim]

Of course, we might want the types to be distinct.  But in this case, it is more likely that we want
the definition to be transparent.  We know that the two kinds of sets are really the
same---@code{Set2} is really just a wrapper for @code{Set}.  How do we establish the equivalence of
@code{'a Set.set} and @code{'a Set2.set}.

The solution is called a @emph{sharing constraint}.  The syntax for a sharing constraint uses the
@code{with} keyword to specify a type equivalence for a module signature in the following form.
@begin[center]
@it{signature} ::= @it{signature} @bf{with type} @it{typename} @bf{=} @it{type}.
@end[center]
In this particular case, we wish to say that the @code{'a Set2.set} type is equal to the @code{'a
Set.set} type, which we can do by adding a sharing constraint when the @code{Set2} module is
defined, as shown in Figure @reffigure[mset8].

@begin[figure,mset8]
@begin[center]
@begin[tabular,lcl]
@line{{@begin[tabular,t,l]
@line{{Module definition}}
@hline
@line{{@bf[module] Set2 : Set2Sig @bf{with type} 'a set = 'a Set.set}}
@line{{= @bf[struct]}}
@line{{$@quad$ @bf[include] Set}}
@line{{$@quad$ @bf[let] add l x = Set.add x l}}
@line{{@bf[end]}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Toploop}}
@hline
@line{{@bf["#"] @bf[let] s = Set2.add Set.empty 1;;}}
@line{{@bf[val] s : int Set2.set = <abstr>}}
@line{{@bf["#"] Set.mem 1 s;;}}
@line{{- : bool = true}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

The constraint specifies that the types @code{'a Set2.set} and @code{'a Set.set} are the same.  In
other words, they @emph{share} a common type.  Since the two types are equal, set values can be
freely passed between the two set implementations.

@section["mod2-summary"]{Summary}

JYH: still to write.

@begin[itemize]
@item{{Simple modules}}
@item{{Modules with multiple signatures}}
@item{{Sharing constraints}}
@end[itemize]

@section["mod2-exercises"]{Exercises}

@begin[enumerate]

@item{{One could argue that sharing constraints are never necessary for unparameterized modules like
the ones in this chapter.  In the example of Figure @reffigure[mset8], there are at least two other
solutions that allow the @code{Set2} and @code{Set} modules to share values, without having to use
sharing constraints.  Present two alternate solutions without sharing constraints.}}

@item{{In OCaml 3.08.3, signatures can apparently contain multiple declarations for the same value.

@begin[iverbatim]
# module type ASig = sig
   val x : int
   val x : bool
  end;;
module type ASig = sig val x : int val x : bool end
@end[iverbatim]

However, these declarations are really just an illusion, only the first declaration counts, any
others are ignored.  Based on what you know, is this behavior expected?  If multiple declarations
are allowed, which one should be the ``real'' declaration?}}

@item{{Unlike @code{val} declarations, @code{type} declarations must have distinct names in any
structure or signature.

@begin[iverbatim]
# module type ASig = sig
     type t = int
     type t = bool
  end;;
Multiple definition of the type name t.
Names must be unique in a given structure or signature.
@end[iverbatim]

While this particular example may seem silly, the real problem is that all modules included with
@bf[include] must have disjoint type names.

@begin[iverbatim]
# module type XSig = sig
     type t
     val x : t
  end;;
# module A : XSig = struct
     type t = bool
     let x = false
  end;;
# module B : XSig = struct
     type t = int
     let x = 0
  end;;
# module C = struct
     include A
     include B
  end;;
Multiple definition of the type name t.
Names must be unique in a given structure or signature.
@end[iverbatim]

Is this a problem?  If it is not, argue that conflicting includes should not be allowed in practice.
If it is, propose a possible solution to the problem.}}

@end[enumerate]

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

>>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
