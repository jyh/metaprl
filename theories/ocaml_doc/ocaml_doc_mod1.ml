doc <:doc< -*- Mode: text -*-
  
   @begin[spelling]
   ADT ADTs Fset acts expr fset goto grep linenum ll
   mem namespace stdin timestep cc ed
   @end[spelling]
  
   @begin[doc]
   @chapter[files]{Files, Compilation Units, and Programs}
   @end[doc]
  
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

doc <:doc< @docoff >>
extends Base_theory

doc <:doc< 
@begin[doc]

One of the principles of modern programming is @emph{data hiding}
using @emph{encapsulation}.  An @emph{abstract data type} (ADT) is a
program unit that defines a data type and functions (also called
@emph{methods}) that operate on that data type.  An ADT has two parts:
a @emph{signature} (or @emph{interface}) that declares the accessible
data structures and methods, and an @emph{implementation} that defines
concrete implementations of the objects declared in the signature.
The implementation is hidden: all access to the ADT must be
through the methods defined in the signature.

There are several ideas behind data hiding using ADTs.
First, by separating a program into distinct program units (called
@emph{modules}), the program may be easier to understand.  Ideally,
each module encapsulates a single concept needed to address the
problem at hand.

Second, by hiding the implementation of a program module,
dependencies between program modules become tightly controlled.  Since
all interactions must be through a module's methods, the
implementation of the module can be changed without affecting the
correctness of the program (as long as the behavior of the methods is
preserved).

OCaml provides a @emph{module system} that makes it easy to use the
concepts of encapsulation and data hiding.  In fact, in OCaml every
program file acts as an abstract module, called a @emph{compilation
unit} in the OCaml terminology.  A signature for the file can
be defined in a @code{.mli} file with the same name.  If there is no
@code{.mli} file, the default signature includes all type and
functions defined in the @code[".ml"] file.

@end[doc]
>>

doc <:doc< 
@begin[doc]

@section[signatures]{Signatures}

In OCaml, a signature contains type definitions and function
declarations for the visible types and methods in the module.  To see
how this works, let's revisit the binary trees we defined in Chapter
@refchapter[unions].  A binary tree defines a simple, distinct
concept, and it is an ideal candidate for encapsulation.

A module signature usually contains three parts:

@begin[enumerate]
@item{Data types used by the module.}
@item{Exceptions used by the module.}
@item{Method type declarations for all the externally visible methods
   defined by the module.}
@end[enumerate]

For the binary tree, the signature will need to include a type
for binary trees, and type declarations for the methods for operating
on the tree.  First, we need to choose a filename for the compilation
unit.  The filename should reflect the @emph{function} of the data
structure defined by the module.  For our purposes, the binary tree is
a data structure used for defining a finite set of values, and
an appropriate filename for the signature would be @code{fset.mli}.

The data structure defines a type for sets, and three methods: an
@tt{empty} set, a @tt{mem} membership function, and an @tt{insert}
insertion function.  The complete signature is defined below; we'll
discuss each of the parts in the following sections.

@begin[verbatim]
(* The abstract type of sets *)
type 'a t

(* Empty set *)
val empty : 'a t

(* Membership function *)
val mem : 'a -> 'a t -> bool

(* Insertion is functional *)
val insert : 'a -> 'a t -> 'a t
@end[verbatim]

@subsection[sig_types]{Type declarations}

Type declarations in a signature can be either @emph{transparent} or
@emph{abstract}.  An abstract type declaration declares a type without
giving the type definition; a transparent type declaration includes
the type definition.

For the binary tree, the declaration @code{type 'a t} is abstract
because the type definition is left unspecified.  In this case, the
type definition won't be visible to other program units; they will be
forced to use the methods if they want to operate on the data type.
Note that the abstract type definition is polymorphic: it is
parameterized by the type variable @code{'a}.

Alternatively, we could have chosen a transparent definition that
would make the type visible to other program modules.  For example, if
we intend to use the unbalanced tree representation, we might include
the following type declaration in the signature.

@begin[verbatim]
type 'a t =
   Node of 'a t * 'a * 'a t
 | Leaf
@end[verbatim]

By doing this, we would make the binary tree structure visible
to other program components; they can now use the type definition to
access the binary tree directly.  This would be
undesirable for several reasons.  First, we may want to change the
representation later (by using red-black trees for example).  If we did
so, we would have to find and modify all the other modules that
accessed the unbalanced structure directly.  Second, we may be
assuming that there are some invariants on values in the data
structure.  For example, we may be assuming that the nodes in the
binary tree are ordered.  If the type definition is visible, it would
be possible for other program modules to construct trees that violate
the invariant, leading to errors that may be difficult to find.

@subsection[method_declarations]{Method declarations}

The method declarations include all the functions and values that are
visible to other program modules.  For the @tt{Fset} module, the
visible methods are the @tt{empty}, @tt{mem}, and @tt{insert}
methods.  The signature gives only the type declarations for these
methods.

It should be noted that @emph{only} these methods will be visible to
other program modules.  If we define helper functions in the
implementation, these functions will be private to the
implementation and inaccessible to other program modules.

@end[doc]
>>

doc <:doc< 
@begin[doc]

@section[implementations]{Implementations}

The module implementation is defined in a @code[".ml"] file with the
same base name as the signature file.  The implementation contains parts
that correspond to each of the parts in the signature.

@begin[enumerate]
@item{Data types used by the module.}
@item{Exceptions used by the module.}
@item{Method definitions.}
@end[enumerate]

The definitions do not have to occur in the same order as declarations in the
signature, but there must be a definition for every item in the
signature.

@subsection[type_definitions]{Type definitions}

In the implementation, definitions must be given for each of the types
in the signature.  The implementation may also include other types.
These types will be private to the implementation; they will
not be visible outside the implementation.

For the @tt{Fset} module, let's use the red-black implementation of
balanced binary trees.  We need two type definitions: the definition
of the @tt{Red} and @tt{Black} labels, and the tree definition itself.

@begin[verbatim]
type color =
   Red
 | Black

type 'a t =
   Node of color * 'a t * 'a * 'a t
 | Leaf
@end[verbatim]

The @tt{color} type is a private type, the @code{'a t} type gives the
type definition for the abstract type declaration @code{type 'a t} in
the signature.

@subsection[method_definitions]{Method definitions}

In the implementation we need to implement each of the methods
declared in the signature.  The @tt{empty} method is easy: the
@tt{Leaf} node is used to implement the empty set.

@begin[verbatim]
let empty = Leaf
@end[verbatim]

The @tt{mem} method performs a search over the binary tree.  The nodes
in the tree are ordered, and we can use a binary search.

@begin[verbatim]
let rec mem x = function
   Leaf -> false
 | Node (_, a, y, b) ->
      if x < y then mem x a
      else if x > y then mem x b
      else true
@end[verbatim]

The implement the @tt{insert} method we need two methods: one is the
actual @tt{insert} function, and another is the helper function
@tt{balance} that keeps the tree balanced.  We can include both
functions in the implementation.  The @tt{balance} function will be
private, since it is not declared in the signature.

@begin[verbatim]
let balance = function
   Black, Node (Red, Node (Red, a, x, b), y, c), z, d ->
      Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
 | Black, Node (Red, a, x, Node (Red, b, y, c)), z, d ->
      Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
 | Black, a, x, Node (Red, Node (Red, b, y, c), z, d) ->
      Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
 | Black, a, x, Node (Red, b, y, Node (Red, c, z, d)) ->
      Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
 | a, b, c, d ->
      Node (a, b, c, d)

let insert x s =
   let rec ins = function
      Leaf -> Node (Red, Leaf, x, Leaf)
    | Node (color, a, y, b) as s ->
         if x < y then balance (color, ins a, y, b)
         else if x > y then balance (color, a, y, ins b)
         else s
   in
      match ins s with  (* guaranteed to be non-empty *)
         Node (_, a, y, b) -> Node (Black, a, y, b)
       | Leaf -> raise (Invalid_argument "insert")
@end[verbatim]

@end[doc]
>>

doc <:doc< 
@begin[doc]

@section[using_comp_unit]{Building a program}

Once a compilation unit is defined, the types and methods can be used
in other files by prefixing the names of the methods with the
@emph{capitalized} file name.  For example, the @tt{empty} set can be
used in another file with the name @code{Fset.empty}.

Let's define another module to test the @code{Fset} implementation.
This will be a simple program with an input loop where we can type in
a string.  If the string is not in the set, it is added;
otherwise, the loop will print out a message that the string is
already added.  To implement this program, we need to add another
file; we'll call it @code["test.ml"].

The @tt{Test} compilation unit has no externally visible types or
methods.  By default, the @code{test.mli} file should be empty.  The
@tt{Test} implementation should contain a function that recursively:

@begin[enumerate]
@item{prints a prompt}
@item{reads a line from @tt{stdin}}
@item{checks if the line is already in the set}
@item{if it is, then print a message}
@item{repeat}
@end[enumerate]

We'll implement this as a @tt{loop} method.

@begin[verbatim]
let loop () =
   let set = ref Fset.empty in
      try
         while true do
            output_string stdout "set> ";
            flush stdout;
            let line = input_line stdin in
               if Fset.mem line !set then
                  Printf.printf "%s is already in the set\n" line
               else
                  Printf.printf "%s added to the set\n" line;
               set := Fset.insert line !set
         done
      with
         End_of_file ->
            ()

let _ = loop ()
@end[verbatim]

There are a few things to note.  First, we need to catch the
@code{End_of_file} exception that is raised when the end of the input
file is reached.  In this case, we exit without comment.  To run the
loop, we include the line @code{let _ = loop ()}.  The
@code{let _ = ...} may seem strange: it tells the OCaml parser that this is a new
top level expression.  Another way to accomplish this is by adding the
@code{;;} terminator after the last @code{()} expression in the
@code{loop} function.

@end[doc]
>>

doc <:doc< 
@begin[doc]

@section[compiling]{Compiling the program}

Once the files for the program are defined, the next step is to
compile them using @tt[ocamlc].  The usage of @tt[ocamlc] is much like
@tt{cc}.  Normally, the files are compiled separately and linked into
an executable.  Signatures must be compiled first, followed by the
implementations.

For the @tt{fset} module, the signature can be compiled with the
following command.

@begin[verbatim]
% ocamlc -c fset.mli
@end[verbatim]

If there are no errors in the signature, this step produces a file
called @code{fset.cmi}.

The implementations are compiled with the following command.

@begin[verbatim]
% ocamlc -c fset.ml
% ocamlc -c test.ml
@end[verbatim]

If this step is successful, the compiler produces the files
@code{fset.cmo} and @code{test.cmo}.

The modules can now be linked into a complete program using the
@tt[ocamlc] linker.  The command is as follows.

@begin[verbatim]
% ocamlc -o test fset.cmo test.cmo
@end[verbatim]

The linker requires all of the @code{.cmo} files to be included in the
program.  The order of these files is important!  Each module in the
link line can refer only to the modules listed @emph{before} it.  If
we reverse the order of the modules on the link line, we will get an
error.

@begin[verbatim]
% ocamlc -o test test.cmo fset.cmo
Error while linking test.cmo: Reference to undefined global `Fset'
Exit 2
@end[verbatim]

Once the program is linked, we can run it.

@begin[verbatim]
% ./test
set> hello
hello added to the set
set> world
world added to the set
set> hello
hello is already in the set
set> x
x added to the set
set> world
world is already in the set
@end[verbatim]

@subsection[main]{Where is the ``main'' function?}

Unlike C programs, OCaml program do not have a ``@tt{main}''
function.  When an OCaml program is evaluated, all the statements in
the files in the program are evaluated in the order specified on the
link line.  Program files contain type and method definitions.  They
can also contain arbitrary expressions to be evaluated.  The @tt{let
_ = loop ()} statement in the @code["test.ml"] file is an example: it
evaluates the @code{loop} function.  Informally, this is the main
loop; it is the last expression to be executed in the program.

@subsection[common_errors]{Some common errors}

When a @code[".ml"] file is compiled, the compiler compares the
implementation with the signature in the @code{.cmi} file.  If a
definition does not match the signature, the compiler will print an
error and refuse to compile the file.

@subsubsection[type_mismatch_error]{Type errors}

For example, suppose we had reversed the order of arguments in the
@code{Fset.insert} function so that the set argument is first.

@begin[verbatim]
let insert s x =
   ...
@end[verbatim]

When we compile the file, we get an error.  The compiler prints the
types of the mismatched values, and exits with an error code.

@begin[verbatim]
% ocamlc -c fset.ml
The implementation fset.ml does not match the interface fset.cmi:
Values do not match:
  val insert : 'a t -> 'a -> 'a t
is not included in
  val insert : 'a -> 'a t -> 'a t
Exit 2
@end[verbatim]

@subsubsection[missing_def_error]{Missing definition errors}

Another common error occurs when a method declared in the signature is
not defined in the implementation.  For example, suppose we had
defined an @tt{add} method rather than an @tt{insert} method.  In this
case, the compiler prints the name of the missing method, and exits
with an error code.

@begin[verbatim]
% ocamlc -c fset.ml
The implementation fset.ml does not match the interface fset.cmi:
The field `insert' is required but not provided
Exit 2
@end[verbatim]

@subsubsection[type_def_errors]{Type definition mismatch errors}

@emph{Transparent} type definitions in the signature can also cause an
error if the type definition in the implementation does not match.
Suppose we were to export the definition for @code{type 'a t}.  We
need to include exactly the same definition in the implementation.
A correct @code{fset.mli} file would contain the following definition.

@begin[verbatim]
type color

type 'a t =
   Node of color * 'a t * 'a * 'a t
 | Leaf
@end[verbatim]

Note that we must include a type definition for @code{color}, since it
is used in the definition of the set type @code{'a t}.  The type
definition for @code{color} may be transparent or abstract.

Now, suppose we reorder the constructors in the interface definition
for @code{'a t} by placing the @code{Leaf} constructor first.

@begin[verbatim]
type color

type 'a t =
   Leaf
 | Node of color * 'a t * 'a * 'a t
@end[verbatim]

When we compile the file, the compiler will produce an error with
the mismatched types.

@begin[verbatim]
% ocamlc -c fset.mli
% ocamlc -c fset.ml
The implementation fset.ml does not match the interface fset.cmi:
Type declarations do not match:
  type 'a t = | Node of color * 'a t * 'a * 'a t | Leaf
is not included in
  type 'a t = | Leaf | Node of color * 'a t * 'a * 'a t
Exit 2
@end[verbatim]

@subsubsection[compile_errors]{Compile dependency errors}

The compiler will also produce errors if the compile state is
inconsistent.  Each time an interface is compile, all the files that
uses that interface must be recompiled.  For example, suppose we
update the @code{fset.mli} file, and recompile it and the
@code{test.ml} file (but we forget to recompile the @code{fset.ml}
file).  The compiler produces the following error.

@begin[verbatim]
% ocamlc -c fset.mli
% ocamlc -c test.ml
% ocamlc -o test fset.cmo test.cmo
Files test.cmo and fset.cmo make inconsistent
assumptions over interface Fset
Exit 2
@end[verbatim]

It takes a little work to detect the cause of the error.  The compiler
says that the files make inconsistent assumptions for interface
@code{Fset}.  The interface is defined in the file @code{fset.cmi},
and so this error message states that at least one of @code{fset.ml}
or @code{test.cmo} needs to be recompiled.  In general, we don't know
which file is out of date, and the best solution is to recompile them
all.

@end[doc]
>>

doc <:doc< 
@begin[doc]

@section[open]{Using @tt{open} to expose a namespace}

Using the full name @tt{@emph{Module_name}.@emph{method_name}} to
refer to the methods in a module can get tedious.  The
@tt{open @emph{Module_name}} statement can be used to ``open'' a module
interface, which will allow the use of unqualified names for types,
exceptions, and methods.  For example, the @code{test.ml} module can
be somewhat simplified by using the @code{open} statements for the
@code{Printf} and @code{Fset} modules.

@begin[verbatim]
open Printf
open Fset

let loop () =
   let set = ref empty in
      try
         while true do
            output_string stdout "set> ";
            flush stdout;
            let line = input_line stdin in
               if mem line !set then
                  printf "%s is already in the set\n" line
               else
                  printf "%s added to the set\n" line;
               set := insert line !set
         done
      with
         End_of_file ->
            ()

let _ = loop ()
@end[verbatim]

Sometimes multiple @tt{open}ed modules will define the same name.  In
this case, the @emph{last} module with an @tt{open} statement will
determine the value of that symbol.  Fully qualified names (of the
form @tt{@emph{Module_name}.@emph{name}}) may still be used even if
the module has been opened.  Fully qualified names can be used to
access values that may have been hidden by an @tt{open} statement.

@subsection[open_errors]{A note about @tt{open}}

Be careful with the use of @tt{open}.  In general, fully qualified
names provide more information, specifying not only the name of the
value, but the name of the module where the value is defined.  For
example, the @tt{Fset} and @tt{List} modules both define a @tt{mem}
function.  In the @tt{Test} module we just defined, it may not be
immediately obvious to a programmer that the @tt{mem} symbol refers
to @code{Fset.mem}, not @code{List.mem}.

In general, you should use @code{open} statement sparingly.  Also, as
a matter of style, it is better not to @tt{open} most of the library
modules, like the @code{Array}, @code{List}, and @code{String}
modules, all of which define methods (like @code{create}) with common
names.  Also, you should @emph{never} @tt{open} the @code{Unix},
@code{Obj}, and @code{Marshal} modules!  The functions in these modules
are not completely portable, and the fully qualified names identify
all the places where portability may be a problem (for instance,
the Unix @tt{grep} command can be used to find all the places where
@code{Unix} functions are used).

The behavior of the @tt{open} statement is not like an @code{#include}
statement in C.  An implementation file @code{mod.ml} should not include
an @code{open Mod} statement.  One common source of errors is defining a type in a
@code{.mli} interface, then attempting to use @code{open} to
``include'' the definition in the @code{.ml} implementation.  This
won't work---the implementation must include an identical type
definition.  True, this is an annoying feature of OCaml.  But it
preserves a simple semantics: the implementation must provide a
definition for each declaration in the signature.

@end[doc]
>>

doc <:doc< 
@begin[doc]

@section[debugging]{Debugging a program}

The @code{ocamldebug} program can be used to debug a program compiled
with @code{ocamlc}.  The @code{ocamldebug} program is a little like
the GNU @code{gdb} program; it allows breakpoints to be set.  When a
breakpoint is reached, control is returned to the debugger so that
program variables can be examined.

To use @code{ocamldebug}, the program must be compiled with the
@code{-g} flag.

@begin[verbatim]
% ocamlc -c -g fset.mli
% ocamlc -c -g fset.ml
% ocamlc -c -g test.ml
% ocamlc -o test -g fset.cmo test.cmo
@end[verbatim]

The debugger is invoked using by specifying the program to be debugged
on the @code{ocamldebug} command line.

@begin[verbatim]
% ocamldebug ./test
	Objective Caml Debugger version 2.04

(ocd) help
List of commands :
cd complete pwd directory kill help quit run reverse step
backstep goto finish next start previous print display source
break delete set show info frame backtrace bt up down last
list load_printer install_printer remove_printer

(ocd)
@end[verbatim]

There are several commands that can be used.  The basic commands are
@code{run}, @code{step}, @code{next}, @code{break}, @code{list},
@code{print}, and @code{goto}.

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

For debugging the @code{test} program, we need to know the line
numbers.  Let's set a breakpoint in the @code{loop} function, which
starts in line 27 in the @code{Test} module.  We'll want to stop at
the first line of the function.

@begin[verbatim]
(ocd) break @ Test 28
Loading program... done.
Breakpoint 1 at 24476 : file Test, line 28 column 4
(ocd) run
Time : 7 - pc : 24476 - module Test
Breakpoint : 1
28    <|b|>let set = ref Fset.empty in
(ocd) n
Time : 8 - pc : 24488 - module Test
29       <|b|>try
(ocd) p set
set : string Fset.t ref = {contents=Fset.Leaf}
@end[verbatim]

Next, let's set a breakpoint after the next input line is read and
continue execution to that point.

@begin[verbatim]
(ocd) list
27 let loop () =
28    let set = ref Fset.empty in
29       <|b|>try
30          while true do
31             output_string stdout "set> ";
32             flush stdout;
33             let line = input_line stdin in
34                if Fset.mem line !set then
35                   Printf.printf "%s is already in the set\n" line
36                else
37                   Printf.printf "%s added to the set\n" line;
38                set := Fset.insert line !set
39          done
(ocd) break @ 34
Breakpoint 2 at 24600 : file Test, line 33 column 40
(ocd) run
set> hello
Time : 22 - pc : 24604 - module Test
Breakpoint : 2
34                <|b|>if Fset.mem line !set then
(ocd) p line
line : string = "hello"
@end[verbatim]

When we run the program, the evaluation prompts us for an input line,
and we can see the value of the line in the @code{line} variable.
Let's continue and view the set after the line is added.

@begin[verbatim]
(ocd) n
Time : 24 - pc : 24628 - module Test
34                if Fset.mem line !set<|a|> then
(ocd) n
Time : 25 - pc : 24672 - module Test
37                   <|b|>Printf.printf "%s added to the set\n" line;
(ocd) n
Time : 135 - pc : 24700 - module Test
37                   Printf.printf "%s added to the set\n" line<|a|>;
(ocd) n
Time : 141 - pc : 24728 - module Test
38                set := Fset.insert line !set<|a|>
(ocd) n
Time : 142 - pc : 24508 - module Test
31             <|b|>output_string stdout "set> ";
(ocd) p set
set : string Fset.t ref =
  {contents=Fset.Node (<abstr>, Fset.Leaf, "hello", Fset.Leaf)}
(ocd)
@end[verbatim]

This value seems to be correct.  Next, suppose we want to go back a
descend into the @code{Fset.mem} function.  We can go back to time
@code{22} (the time just before the @code{Fset.mem} function is called),
and use the @code{step} command to descend into the membership
function.

@begin[verbatim]
(ocd) goto 22
set> hello
Time : 22 - pc : 24604 - module Test
Breakpoint : 7
34                <|b|>if Fset.mem line !set then
(ocd) s
Time : 23 - pc : 22860 - module Fset
39    Leaf -> <|b|>false
(ocd) s
Time : 24 - pc : 24628 - module Test
34                if Fset.mem line !set<|a|> then
(ocd)
@end[verbatim]

Note that when we go back in time, the program prompts us again for an
input line.  This is due to way time travel is implemented in
@code{ocamldebug}.  Periodically, the debugger takes a checkpoint of
the program (using the Unix @code{fork()} system call).  When reverse
time travel is requested, the debugger restarts the program from the
closest checkpoint before the time requested.  In this case, the
checkpoint was taken sometime before the call to @code{input_line},
and the program resumption requires another input value.

When we step into the @code{Fset.mem} function, we see that the
membership is false (the set is the @code{Leaf} empty value).  We can
continue from here, examining the remaining functions and variables.
You may wish to explore the other features of the debugger.  Further
documentation can be found in the OCaml reference manual.

@end[doc]
@docoff
>>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
