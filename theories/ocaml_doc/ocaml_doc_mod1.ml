(* -*- Mode: text; fill-column: 100 -*- *)
doc <:doc<

   @begin[spelling]
   ADT ADTs Fset acts expr fset goto grep linenum ll
   mem namespace stdin timestep cc ed
   @end[spelling]

   @chapter[files]{Files, Compilation Units, and Programs}

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

Until now, we have been writing programs using the OCaml toploop.  As programs get larger, it is
natural to want to save them in files so that they can be re-used and shared with others.  There are
other advantages to doing so, including the ability to partition a program into multiple files that
can be written and compiled separately, making it easier to construct and maintain the program.
Perhaps the most important reason to use files is that they serve as @emph{abstraction boundaries}
that divide a program into conceptual parts.  We will see more about abstraction during the next few
chapters as we cover the OCaml module system, but for now let's begin with an example of a complete
program implemented in a single file.

@section["uniq-example"]{Single-file programs}

For this example, let's build a simple program that removes duplicate lines in an input file.  That
is, the program should read its input a line at a time, printing the line only if it hasn't seen it
before.

One of the simplest implementations is to use a list to keep track of which lines have been read.
The program can be implemented as a single recursive function that 1) reads a line of input, 2)
compares it with lines that have been previously read, and 3) outputs the line if it has not been
read.  The entire program is implemented in the single file @code{unique.ml}, shown in Figure
@reffigure[uniq1] with an example run.

In this case, we can compile the entire program in a single step with the command @code{ocamlc -o
unique unique.ml}, where @code{ocamlc} is the OCaml compiler, @code{unique.ml} is the program file,
and the @code{-o} option is used to specify the program executable @code{unique}.

@begin[figure,uniq1]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{File: @code{unique.ml}}}
@hline
@line{{@bf[let] @bf[rec] unique already_read =}}
@line{{$@quad$ output_string stdout @code{"> ";}}}
@line{{$@quad$ flush stdout;}}
@line{{$@quad$ @bf[let] line = input_line stdin @bf[in]}}
@line{{$@quad @quad$ @bf[if] not (List.mem line already_read) @bf{then begin}}}
@line{{$@quad @quad @quad$ output_string stdout line;}}
@line{{$@quad @quad @quad$ output_char stdout @code{'\n'};}}
@line{{$@quad @quad @quad$ unique (line :: already_read)}}
@line{{$@quad @quad$ @bf[end] @bf[else]}}
@line{{$@quad @quad @quad$ unique already_read;;}}
@line{{}}
@line{{@it{{(}{*} ``Main program'' {*}{)}}}}
@line{{@bf[try] unique {[{}]} @bf[with]}}
@line{{$@quad$ End_of_file ->}}
@line{{$@quad @quad$ ();;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Example run}}
@hline
@line{{@code{%} ocamlc -o unique unique.ml}}
@line{{@code{%} ./unique}}
@line{{@code{>} Great Expectations}}
@line{{Great Expectations}}
@line{{@code{>} Vanity Fair}}
@line{{Vanity Fair}}
@line{{@code{>} The First Circle}}
@line{{The First Circle}}
@line{{@code{>} Vanity Fair}}
@line{{@code{>} Paradise Lost}}
@line{{Paradise Lost}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

@subsection[main]{Where is the main function?}

Unlike C programs, OCaml program do not have a ``@tt{main}'' function.  When an OCaml program is
evaluated, all the statements in the implementation files are evaluated.  In general, implementation
files can contain arbitrary expressions, not just function definitions.  For this example, the
``main program'' is the @bf[try] expression in the @code{unique.ml} file, which gets evaluated when the
@code{unique.cmo} file is evaluated.

@subsection[compilers]{OCaml compilers}

The INRIA OCaml implementation, most likely the one you are using,  provides two compilers---the
@code{ocamlc} byte-code compiler, and the @code{ocamlopt} native-code compiler.  Programs compiled
with @code{ocamlc} are @emph{interpreted}, while programs compiled with @code{ocamlopt} are compiled
to native machine code to be run on a specific operating system and machine architecture.  While the
two compilers produce programs that behave identically functionally, there are a few differences.

@begin[enumerate]

@item{{Compile time is shorter with the @code{ocamlc} compiler.  Compiled byte-code is portable to
any operating system and architecture supported by OCaml, without the need to recompile.  Some
tasks, like debugging, work only with byte-code executables.}}

@item{{Compile time is longer with the @code{ocamlopt} compiler, but program execution is usually
faster.  Program executables are not portable, and not every operating system and machine
architecture is supported.}}

@end[enumerate]

We generally won't be concerned with the compiler being used, since the two compilers produce
programs that behave identically (arapart from performance).  During rapid development, it may be
useful to use the byte-code compiler because compilation times are shorter.  If performance becomes
an issue, it is usually a straightforward process to begin using the native-code compiler.

@section["multiple-files"]{Multiple files and abstraction}

OCaml uses files as a basic unit for providing data hiding and encapsulation, two important
properties that can be used to strengthen the guarantees provided by the implementation.  We will
see more about data hiding and encapsulation in Chapter @refchapter[modules], but for now the
important part is that each file can be assigned a @emph{interface} that declares types for all the
accessible parts of the implementation, and everything @emph{not} declared is inaccessible outside
the file.

In general, a program will have many files and interfaces.  An implementation file is defined in a
file with a @code{.ml} suffix, called a @emph{compilation unit}.  An interface for a file
@emph{filename.ml} is defined in a file named @emph{filename.mli}.  There are four major steps to
planning and building a program.

@begin[enumerate]

@item{{Decide how to @emph{factor} the program into separate parts.  Each part will be implemented
in a separate compilation unit.}}

@item{{Implement each of compilation units as a file with a @code{.ml} suffix, and optionally define
an interface for the compilation unit in a file with a @code{.mli} suffix.}}

@item{{Compile each file and interface with the OCaml compiler.}}

@item{{Link the compiled files to produce an executable program.}}

@end[enumerate]

One nice consequence of implementing the parts of a program in separate files is that each file can
be compiled separately.  When a project is modified, only the files that are affected must be
recompiled; there is there is usually no need to recompile the entire project.

Getting back to the example @code{unique.ml}, the implementation is already too concrete.  We chose
to use a list to represent the set of lines that have been read, but one problem with using lists is
that checking for membership (with @code{List.mem}) takes time linear in the length of the list,
which means that the time to process a file is quadratic in the number of lines in the file!  There
are clearly better data structures than lists for the set of lines that have been read.

As a first step, let's partition the program into two files.  The first file @code{set.ml} is to
provide a generic implementation of sets, and the file @code{unique.ml} provides the @code{unique}
function as before.  For now, we'll keep the list representation in hopes of improving it
later---for now we just want to factor the project.

@begin[figure,uniq2]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{File: set.ml}}
@hline
@line{{@bf[let] empty = []}}
@line{{@bf[let] add x l = x @code{::} l}}
@line{{@bf[let] mem x l = List.mem x l}}
@line{{}}
@line{{File: unique.ml}}
@hline
@line{{@bf[let] @bf[rec] unique already_read =}}
@line{{$@quad$ output_string stdout @code{"> ";}}}
@line{{$@quad$ flush stdout;}}
@line{{$@quad$ @bf[let] line = input_line stdin @bf[in]}}
@line{{$@quad @quad$ @bf[if] not (Set.mem line already_read) @bf{then begin}}}
@line{{$@quad @quad @quad$ output_string stdout line;}}
@line{{$@quad @quad @quad$ output_char stdout @code{'\n'};}}
@line{{$@quad @quad @quad$ uniq (line :: already_read)}}
@line{{$@quad @quad$ @bf[end] @bf[else]}}
@line{{$@quad @quad @quad$ unique already_read;;}}
@line{{}}
@line{{@it{{(}{*} Main program {*}{)}}}}
@line{{@bf[try] unique [] @bf[with]}}
@line{{$@quad$ End_of_file ->}}
@line{{$@quad @quad$ ();;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Example run}}
@hline
@line{{@code{%} ocamlc -c set.ml}}
@line{{@code{%} ocamlc -c unique.ml}}
@line{{@code{%} ocamlc -o unique set.cmo unique.cmo}}
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

The new project is shown in Figure @reffigure[uniq2].  We have split the set operations into a file
called @code{set.ml}, and instead of using the @code{List.mem} function we now use the
@code{Set.mem} function.  This naming convention is standard throughout OCaml---the way to refer to a
definition $f$ in a file named @emph{filename} is by capitalizing the filename and using the infix
@code{.} operator to project the value.  The @code{Set.mem} expression refers to the @code{mem}
function in the @code{set.ml} file.  In fact, the @code{List.mem} function is the same way.  The
OCaml standard library contains a file @code{list.ml} that defines a function @code{mem}.

Compilation is now several steps.  In the first step, the @code{set.ml} and @code{unique.ml} files
are compiled with the @code{-c} option, which specifies that the compiler should produce an
intermediate file with a @code{.cmo} suffix.  These files are then linked to produce an executable
with the command @code{ocamlc -o unique set.cmo unique.cmo}.

The order of compilation and linking here is significant.  The @code{unique.ml} file refers to the
@code{set.ml} file by using the @code{Set.mem} function.  Due to this dependency, the @code{set.ml}
file must be compiled before the @code{unique.ml} file, and the @code{set.cmo} file must appear before
the @code{unique.cmo} file during linking.  Note that cyclic dependencies are @emph{not allowed}.  It
is not legal to have a file @code{a.ml} refer to a value @code{B.x}, and a file @code{b.ml} that
refers to a value @code{A.y}.

@subsection["defining-signature"]{Defining a signature}

One of the reasons for factoring the program was to be able to improve the implementation of sets.
To begin, we should make the type of sets @emph{abstract}---that is, we should hide the details of
how it is implemented so that we can be sure the rest of the program does not uninitentionally
depend on the implementation details.  To do this, we can define an abstract signature for sets, in
a file @code{set.mli}.

A signature should declare types for each of the values that are publicly accessible in a module, as
well as any needed type declarations or definitions.  For our purposes, we need to define a
polymorphic type of sets @code{'a set} abstractly.  That is, in the signature we will declare a type
@code{'a set} without giving a definition, preventing other parts of the program from knowing, or
depending on, the particular representation of sets we have chosen.  The signature also needs to
declare types for the public values @code{empty}, @code{add}, and @code{mem} values, as a
declaration of the form ``@bf{val} @it{name} : @it{type}''.  The complete signature is shown in
Figure @reffigure[uniq3].  The implementation remains mostly unchanged, except that a specific,
concrete type definition must be given for the type @code{'a set}.

@begin[figure,uniq2]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{File: set.mli}}
@hline
@line{{@bf[type] 'a set}}
@line{{@bf[val] empty : 'a set}}
@line{{@bf[val] add   : 'a -> 'a set -> 'a set}}
@line{{@bf[val] mem   : 'a -> 'a set -> bool}}
@line{{}}
@line{{File: set.ml}}
@hline
@line{{@bf[type] 'a set = 'a list}}
@line{{@bf[let] empty = []}}
@line{{@bf[let] add x l = x @code{::} l}}
@line{{@bf[let] mem x l = List.mem x l}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Example run}}
@hline
@line{{@code{%} ocamlc -c set.mli}}
@line{{@code{%} ocamlc -c set.ml}}
@line{{@code{%} ocamlc -c uniq.ml}}
@line{{File "uniq.ml", line 8, characters 14-36:}}
@line{{This expression has type 'a list but is}}
@line{{$@quad$ here used with type string Set.set}}
@end[tabular]}}

@line{{} {} {}}
@line{
{@begin[tabular,t,l]
@line{{File: uniq.ml}}
@hline
@line{{@bf[let] @bf[rec] uniq already_read =}}
@line{{$@quad$ output_string stdout @code{"> ";}}}
@line{{$@quad$ flush stdout;}}
@line{{$@quad$ @bf[let] line = input_line stdin @bf[in]}}
@line{{$@quad @quad$ @bf[if] not (Set.mem line already_read) @bf[then] @bf[begin]}}
@line{{$@quad @quad @quad$ output_string stdout line;}}
@line{{$@quad @quad @quad$ output_char stdout @code{'\n'};}}
@line{{$@quad @quad @quad$ @it{{(}{*} uniq (line :: already_read) {*}{)}}}}
@line{{$@quad @quad @quad$ uniq (Set.add line already_read)}}
@line{{$@quad @quad$ @bf[end] @bf[else]}}
@line{{$@quad @quad @quad$ uniq already_read;;}}
@line{{}}
@line{{@it{{(}{*} Main program {*}{)}}}}
@line{{@bf[try] uniq Set.empty @bf[with]}}
@line{{$@quad$ End_of_file ->}}
@line{{$@quad @quad$ ();;}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{Example run}}
@hline
@line{{@code{%} ocamlc -c set.mli}}
@line{{@code{%} ocamlc -c set.ml}}
@line{{@code{%} ocamlc -c uniq.ml}}
@line{{@code{%} ocamlc -o uniq set.cmo uniq.cmo}}
@line{{@code{%} ./uniq}}
@line{{@code{>} Siddhartha}}
@line{{Siddhartha}}
@line{{@code{>} Siddhartha}}
@line{{@code{>} Siddharta}}
@line{{Siddharta}}
@end[tabular]}}

@end[tabular]
@end[center]
@end[figure]

Now, when we compile the program, we first compile the interface file @code{set.mli}, then the
implementations @code{set.ml} and @code{uniq.ml}.  But something has changed, the @code{uniq.ml}
file no longer compiles!  Following the error message, we find that the error is due to the
expression @code{line :: already_read}, which uses a @code{List} operation instead of a @code{Set}
operation.  Since the @code{'a set} type is abstract, it is now an error to treat the set as a list,
and the compiler complains appropriately.

Changing this expression to @code{Set.add line already_read} fixes the error.  Note that, while the
@code{set.mli} file must be compiled, it does not need to be specified during linking @code{ocamlc
-o uniq set.cmo uniq.cmo}.

At this point, the @code{set.ml} implementation is fully abstract, making it easy to replace the
implementation with a better one (for example, the implementation of sets using red-black trees in
Chapter @refchapter["red-black"]).

@subsection["transparent-types"]{Transparent type definitions}

In some cases, abstract type definitions are too strict.  There are times when we want a type
definition to be @emph{transparent}---that is, visible outside the file.  For example, suppose we
wanted to add a @code{choose} function to the set implementation, where, given a set $s$, the
expression (@code{choose} $s$) returns some element of the set if the set is non-empty, and nothing
otherwise.  One possible way to write this function is to define a union type @code{choice} that
defines the two cases, as shown in Figure @reffigure[uniq4].

The type definition for @code{choice} must be transparent (otherwise there isn't much point in
defining the function).  For the type to be transparent, the signature simply need to provide the
definition.  The implementation must contain the @emph{same} definition.

@begin[figure,uniq4]
@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{File: set.mli}}
@hline
@line{{@bf[type] 'a set}}
@line{{@bf[type] 'a choice =}}
@line{{$@quad$ | Element of 'a}}
@line{{$@quad$ | Empty}}
@line{{@bf[val] empty  : 'a set}}
@line{{@bf[val] add    : 'a -> 'a set -> 'a set}}
@line{{@bf[val] mem    : 'a -> 'a set -> bool}}
@line{{@bf[val] choose : 'a set -> 'a choice}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{File: set.ml}}
@hline
@line{{@bf[type] 'a set = 'a list}}
@line{{@bf[type] 'a choice =}}
@line{{$@quad$ | Element of 'a}}
@line{{$@quad$ | Empty}}
@line{{@bf[let] empty = []}}
@line{{@bf[let] add x l = x @code{::} l}}
@line{{@bf[let] mem x l = List.mem x l}}
@line{{@bf[let] choose = @bf[function]}}
@line{{$@quad$ | x :: _ -> Element x}}
@line{{$@quad$ | [] -> Empty}}
@end[tabular]}}
@end[tabular]
@end[center]
@end[figure]

@section["common-errors"]{Some common errors}

As you develop programs with several files, you will undoubtably encounter some errors.  The
following subsections list some of the more common errors.

@subsection["interface-errors"]{Interface errors}

When a @code[".ml"] file is compiled, the compiler compares the implementation with the signature in
a @code{.cmi} file compile from the @code{.mli} file.  If a definition does not match the signature,
the compiler will print an error and refuse to compile the file.

@subsubsection["type-mismatch-error"]{Type errors}

For example, suppose we had reversed the order of arguments in the @code{Set.add} function so that
the set argument is first.

@begin[iverbatim]
let add s x = x :: s
@end[iverbatim]

When we compile the file, we get an error.  The compiler prints the types of the mismatched values,
and exits with an error code.

@begin[iverbatim]
% ocamlc -c set.mli
% ocamlc -c set.ml
The implementation set.ml does not match the interface set.cmi:
Values do not match:
  val add : 'a list -> 'a -> 'a list
is not included in
  val add : 'a -> 'a set -> 'a set
@end[iverbatim]

The first declaration is the type the compiler infered for the definition; the second declaration is
from the signature.  Note that the definition's type is not abstract (using @code{'a list} instead
of @code{'a set}).  For this example, it is clear that the argument ordering doesn't match, and the
definition or the signature must be changed.

@subsubsection["missing-def-error"]{Missing definition errors}

Another common error occurs when a function declared in the signature is not defined in the
implementation.  For example, suppose we had defined an @tt{insert} function istead of an @tt{add}
function.  In this case, the compiler prints the name of the missing function, and exits with an
error code.

@begin[iverbatim]
% ocamlc -c set.ml
The implementation set.ml does not match the interface set.cmi:
The field `add' is required but not provided
@end[iverbatim]

@subsubsection["type-def-errors"]{Type definition mismatch errors}

@emph{Transparent} type definitions in the signature can also cause an error if the type definition
in the implementation does not match.  For example, in the definition of the @code{choice} type,
suppose we had declared the cases in different orders.

@begin[center]
@begin[tabular,lcl]
@line{
{@begin[tabular,t,l]
@line{{File: set.mli}}
@hline
@line{{@bf[type] 'a set}}
@line{{@bf[type] 'a choice =}}
@line{{$@quad$ | Element of 'a}}
@line{{$@quad$ | Empty}}
@line{{$@vdots$}}
@end[tabular]}
{$@quad$}
{@begin[tabular,t,l]
@line{{File: set.ml}}
@hline
@line{{@bf[type] 'a set = 'a list}}
@line{{@bf[type] 'a choice =}}
@line{{$@quad$ | Empty}}
@line{{$@quad$ | Element of 'a}}
@line{{$@vdots$}}
@end[tabular]}}
@end[tabular]
@end[center]

When we compile the @code{set.ml} file, the compiler will produce an error with
the mismatched types.

@begin[iverbatim]
% ocamlc -c set.mli
% ocamlc -c set.ml
The implementation set.ml does not match the interface set.cmi:
Type declarations do not match:
  type 'a choice = Empty | Element of 'a
is not included in
  type 'a choice = Element of 'a | Empty
@end[iverbatim]

The type definitions are required to be @emph{exactly} the same.  Some programmers find this
duplication of type definitions to be annoying.  While it is difficult to avoid all duplication of
type definitions, one common solution is to define the transparent types in a separate @code{.ml}
file without a signature, for example by moving the definition of @code{'a choice} to a file
@code{set_types.ml}.  By default, when an interface file does not exist, all definitions from the
implementation are fully visible.  As a result, the type in @code{set_types.ml} needs to be defined
just once.

@subsubsection["compile-errors"]{Compile dependency errors}

The compiler will also produce errors if the compile state is inconsistent.  Each time an interface
is compile, all the files that uses that interface must be recompiled.  For example, suppose we
update the @code{set.mli} file, and recompile it and the @code{uniq.ml} file (but we forget to
recompile the @code{set.ml} file).  The compiler produces the following error.

@begin[iverbatim]
% ocamlc -c set.mli
% ocamlc -c uniq.ml
% ocamlc -o uniq set.cmo uniq.cmo
Files uniq.cmo and set.cmo make inconsistent
assumptions over interface Set
@end[iverbatim]

It takes a little work to detect the cause of the error.  The compiler says that the files make
inconsistent assumptions for interface @code{Set}.  The interface is defined in the file
@code{set.cmi}, and so this error message states that at least one of @code{set.ml} or
@code{uniq.ml} needs to be recompiled.  In general, we don't know which file is out of date, and
the best solution is usually to recompile them all.

@section[open]{Using @tt{open} to expose a namespace}

Using the full name @tt{@emph{File_name}.@emph{name}} to refer to the values in a module can get
tedious.  The @tt{open @emph{File_name}} statement can be used to ``open'' an interface, allowing
the use of unqualified names for types, exceptions, and values.  For example, the @code{unique.ml}
module can be somewhat simplified by using the @code{open} directive for the @code{Set} module.  In
the following listing, the @underline{underlined} variables refer to the value in the Set
implementation.

@begin[center]
@begin[tabular,t,l]
@line{{File: uniq.ml}}
@hline
@line{{@bf[open] Set}}
@line{{@bf[let] @bf[rec] uniq already_read =}}
@line{{$@quad$ output_string stdout @code{"> ";}}}
@line{{$@quad$ flush stdout;}}
@line{{$@quad$ @bf[let] line = input_line stdin @bf[in]}}
@line{{$@quad @quad$ @bf[if] not (@underline{mem} line already_read) @bf[then] @bf[begin]}}
@line{{$@quad @quad @quad$ output_string stdout line;}}
@line{{$@quad @quad @quad$ output_char stdout @code{'\n'};}}
@line{{$@quad @quad @quad$ uniq (@underline{add} line already_read)}}
@line{{$@quad @quad$ @bf[end] @bf[else]}}
@line{{$@quad @quad @quad$ uniq already_read;;}}
@line{{}}
@line{{@it{{(}{*} Main program {*}{)}}}}
@line{{@bf[try] uniq @underline{empty} @bf[with]}}
@line{{$@quad$ End_of_file ->}}
@line{{$@quad @quad$ ();;}}
@end[tabular]
@end[center]

Sometimes multiple @tt{open}ed files will define the same name.  In this case, the @emph{last} file
with an @tt{open} statement will determine the value of that symbol.  Fully qualified names (of the
form @tt{@emph{File_name}.@emph{name}}) may still be used even if the file has been opened.  Fully
qualified names can be used to access values that may have been hidden by an @tt{open} statement.

@subsection["open-errors"]{A note about @tt{open}}

Be careful with the use of @tt{open}.  In general, fully qualified names provide more information,
specifying not only the name of the value, but the name of the module where the value is defined.
For example, the @tt{Set} and @tt{List} modules both define a @tt{mem} function.  In the @tt{Uniq}
module we just defined, it may not be immediately obvious to a programmer that the @tt{mem} symbol
refers to @code{Set.mem}, not @code{List.mem}.

In general, you should use @code{open} statement sparingly.  Also, as a matter of style, it is
better not to @tt{open} most of the library modules, like the @code{Array}, @code{List}, and
@code{String} modules, all of which define methods (like @code{create}) with common names.  Also,
you should @emph{never} @tt{open} the @code{Unix}, @code{Obj}, and @code{Marshal} modules!  The
functions in these modules are not completely portable, and the fully qualified names identify all
the places where portability may be a problem (for instance, the Unix @tt{grep} command can be used
to find all the places where @code{Unix} functions are used).

The behavior of the @tt{open} statement is not like an @code{#include} statement in C.  An
implementation file @code{mod.ml} should not include an @code{open Mod} statement.  One common
source of errors is defining a type in a @code{.mli} interface, then attempting to use @code{open}
to ``include'' the definition in the @code{.ml} implementation.  This won't work---the
implementation must include an identical type definition.  True, this might be considered to be an
annoying feature of OCaml.  But it preserves a simple semantics: the implementation must provide a
definition for each declaration in the signature.

@section[debugging]{Debugging a program}

The @code{ocamldebug} program can be used to debug a program compiled with @code{ocamlc}.  The
@code{ocamldebug} program is a little like the GNU @code{gdb} program; it allows breakpoints to be
set.  When a breakpoint is reached, control is returned to the debugger so that program variables
can be examined.

To use @code{ocamldebug}, the program must be compiled with the
@code{-g} flag.

@begin[iverbatim]
% ocamlc -c -g set.mli
% ocamlc -c -g set.ml
% ocamlc -c -g uniq.ml
% ocamlc -o uniq -g set.cmo uniq.cmo
@end[iverbatim]

The debugger is invoked using by specifying the program to be debugged
on the @code{ocamldebug} command line.

@begin[iverbatim]
% ocamldebug ./uniq
	Objective Caml Debugger version 3.08.3

(ocd) help
List of commands :cd complete pwd directory kill help quit shell run reverse
step backstep goto finish next start previous print display source break
delete set show info frame backtrace bt up down last list load_printer
install_printer remove_printer
@end[iverbatim]

There are several commands that can be used.  The basic commands are
@code{run}, @code{step}, @code{next}, @code{break}, @code{list},
@code{print}, and @code{goto}.

@begin[quote]
@begin[description]
@item{run; Start or continue execution of the program.}
@item{break @@ module linenum; Set a breakpoint on line @emph{linenum}
   in module @emph{module}.}
@item{list; display the lines around the current execution point.}
@item{print expr; Print the value of an expression.  The expression
   must be a variable.}
@item{goto time; Execution of the program is measured in time steps,
   starting from 0.  Each time a breakpoint is reached, the debugger
   will print the current time.  The @code{goto} command may be used
   to continue execution to a future time, or to a @emph{previous}
   timestep.}
@item{step; Go forward one time step.}
@item{next; If the current value to be executed is a function,
   evaluate the function, a return control to the debugger when the
   function completes.  Otherwise, step forward one time step.}
@end[description]
@end[quote]

For debugging the @code{uniq} program, we need to know the line
numbers.  Let's set a breakpoint in the @code{uniq} function, which
starts in line 1 in the @code{Uniq} module.  We'll want to stop at
the first line of the function.

@begin[iverbatim]
(ocd) break @ Uniq 1
Loading program... done.
Breakpoint 1 at 21656 : file uniq.ml, line 2, character 4
(ocd) run
Time : 12 - pc : 21656 - module Uniq
Breakpoint : 1
2    <|b|>output_string stdout "> ";
(ocd) n
Time : 14 - pc : 21692 - module Uniq
2    output_string stdout "> "<|a|>;
(ocd) n
> Time : 15 - pc : 21720 - module Uniq
3    flush stdout<|a|>;
(ocd) n
Robinson Crusoe
Time : 29 - pc : 21752 - module Uniq
5       <|b|>if not (Set.mem line already_read) then begin
(ocd) p line
line : string = "Robinson Crusoe"
@end[iverbatim]

Next, let's set a breakpoint just before calling the @code{uniq} function recursively.

@begin[iverbatim]
(ocd) list
1 let rec uniq already_read =
2    output_string stdout "> ";
3    flush stdout;
4    let line = input_line stdin in
5       <|b|>if not (Set.mem line already_read) then begin
6          output_string stdout line;
7          output_char stdout '\n';
8          uniq (Set.add line already_read)
9       end
10       else
11          uniq already_read;;
12
13 (* Main program *)
14 try uniq Set.empty with
15    End_of_file ->
16       ();;
Position out of range.
(ocd) break @ 8
Breakpoint 2 at 21872 : file uniq.ml, line 8, character 42
(ocd) run
Time : 38 - pc : 21872 - module Uniq
Breakpoint : 2
8          uniq (Set.add line already_read)<|a|>
@end[iverbatim]

Next, suppose we don't like adding this line.  We can go back to time @code{15} (the time just
before the @code{input_line} function is called).

@begin[iverbatim]
(ocd) goto 15
> Time : 15 - pc : 21720 - module Uniq
3    flush stdout<|a|>;
(ocd) n
Mrs Dalloway
Time : 29 - pc : 21752 - module Uniq
5       <|b|>if not (Set.mem line already_read) then begin
@end[iverbatim]

Note that when we go back in time, the program prompts us again for an input line.  This is due to
way time travel is implemented in @code{ocamldebug}.  Periodically, the debugger takes a checkpoint
of the program (using the Unix @code{fork()} system call).  When reverse time travel is requested,
the debugger restarts the program from the closest checkpoint before the time requested.  In this
case, the checkpoint was taken before the call to @code{input_line}, and the program resumption
requires another input value.

We can continue from here, examining the remaining functions and variables.  You may wish to explore
the other features of the debugger.  Further documentation can be found in the OCaml reference
manual.

>>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
