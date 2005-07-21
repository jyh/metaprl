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
some parts of a data structre are abstract but others are directly accessible.  OCaml provides a
general mechanism for data hiding and encapsulation called a @emph{module system}.  An module in
OCaml has two parts: an @emph{implementation} that implements the types, functions, and values in
the module; and a @emph{signarture} that specifies which parts of the implementation are publically
accessible.  That is, a signature provides type declarations for the visible parts of the
implementation---everything else is hidden.

In fact, in OCaml every source file is a module called a @emph{compilation unit}.  Signatures are
specified in separate files called @emph{interfaces}.  In general, a program will have many files
and signatures for its modules, where each module represents a program (and compilation) unit that
implements part of the program.  When planning an application, the first step is
@emph{factoring}---deciding how to partition the application into its parts.  The next step is then
to implement the parts.  Normally in OCaml, this starts with the @emph{signatures} rather than the
implementations because the signatures summarize the requirements and determine what must be
implemented.

@section[signatures]{Signatures}

In OCaml, a signature contains declarations for the types and values in the implementation.
A interface file has a @code{.mli} suffix.  The interface has three main parts.

@begin[enumerate]
@item{type definitions and declarations,},
@item{any exceptions defined in the module,}
@item{declarations for any public functions and values defined by the module.}
@end[enumerate]

To illustrate, let's build a simple database-style application, where we will have a set of accounts
indexed by number.  For example, we might be building a banking system where each account has a
number, the name of the owner, and the account balance.  Instead of defining the entire application
in one file, we can factor this application by breaking it into two parts, where the first part is a
generic (polymorphic) table indexed by number, and the second adds a concrete definition of the
account format.

The first step is to define a signature for the generic table.  We'll need functions to create a new
table, and to store and fetch entries from the table.  We'll also include a function to copy the
table.  Since there is no reason to expose the representation of the table, the type is defined as
abstract.  The following signature, in the file @code{table.mli}, specifies the complete table.

@begin[iverbatim]
(* -- File: table.mli -- *)
(* The abstract type of tables *)
type 'a t

(* Create a new table *)
val create : unit -> 'a t

(* Fetch an entry from the table.
 * Raises the Not_found exception if the entry
 * doesn't exist *)
val get : 'a t -> int -> 'a

(* Set an entry in the table *)
val set : 'a t -> int -> 'a -> unit

(* Copy the table *)
val copy : 'a t -> 'a t
@end[iverbatim]

Note that the type declaration @code{type 'a t} does not provide a definition (of the form
@code{type 'a t = ...}).  This is an @emph{abstract} declaration stating that @code{'a t} is a type,
but the specific representation is not publically visible.  The functions in the signature are
declared with the @code{val} keyword. giving the name and the type of the function.  The function
types use the abstract @code{'a t} type, but it should be clear from the declarations that the only
way to create a new table is with the @code{create} function.

For the next step, let's define a signature for a bank account database.  For this module, we want
the type of accounts to be transparent (visible).  We will need functions to perform the usual
operations for withdrawal, deposit, and account transfer.  In our simple bank, we won't allow
accounts to be overdrawn, so we'll include an exception @code{Overdrawn}.

@begin[iverbatim]
(* -- File: bank.mli -- *)
(* Accounts are specified by number *)
type account = int

(* Information about an account *)
type account_info = { owner : string; balance : float }

(* Exception for overdrawn accounts *)
exception Overdrawn of account

(* Get the information for an account *)
val query : account -> account_info

(* Withdraw from the account, may raise Overdrawn. *)
val withdraw : account -> float -> unit
val deposit  : account -> float -> unit

(* Perform several account transfers at once.
 * If any account would be overdrawn, it raises
 * the Overdrawn exception and has no effect. *)
val transaction : (account * account * float) list -> unit
@end[iverbatim]

In this signature, the types @code{account} and @code{account_info} are @emph{transparent}, meaning
that their definitions are given (without this, the @code{query} function would be rather useless).
The @code{transaction} function is intended to perform multiple transfers at once.  If any of them
fail because of an overdrawn account, the entire transaction should be aborted and the
@code{Overdrawn} exception raised.

As these signatures show, an interface is a collection of declarations for the types (both
transparent and abstract), exceptions, and values.  Once the signatures are defined, the next step
is to implement them.

@section["implementation"]{Implementations}

A module implementation is defined in a @code[".ml"] file with the same base name as the signature
file.  For each part of the signature, there is a corresponding definition in the implementation.
An implementation has the following parts:

@begin[enumerate]
@item{type definitions,}
@item{exception definitions,}
@item{function and value definitions.}
@end[enumerate]

@subsection["table-implementation"]{Table implementation}

Let's return to the bank example, beginning with the implementation of a generic table indexed by
number.  One possible implementation is as a hash table, with an array of buckets index by hashed
account number.  To keep the example managable, we'll use a fixed-size hash table.  For the first
step, we define the type @code{'a t} as an array of buckets, where each bucket is a list of entries
and their index.  The @code{create} function creates a new array of empty buckets for the table,
using the @code{Array.create} function.  In addition, the @code{copy} function uses the
@code{Array.copy} function to duplicate the table.

@begin[iverbatim]
(* -- File: table.ml -- *)
(* The type of hash tables is an array of entry lists *)
type 'a t = (int * 'a) list array

(* Large, fixed-size table *)
let create () = Array.create table_size 100000

(* Copy the table *)
let copy table = Array.copy table
@end[iverbatim]

Let's implement the @code{get} function next.  For this, we need to search for an entry in the table
based on its hash index.  To implement this, the @code{get} function must search through the bucket
based on the hashed index.  We define two helper functions: the @code{hash} function computes the
hash of the index, and the @code{find_in_bucket} function search the bucket for the entry.  Since
these functions are not declare in the signature, they are @emph{private} to this implementation.

@begin[iverbatim]
(* -- File: table.ml (continued) -- *)
(* Simple hash into the table *)
let hash table index =
   index mod (Array.length table)

(* Find an entry in the bucket *)
let rec find_in_bucket index bucket =
   match bucket with
      (index', entry) :: _ when index' = index ->
         entry
    | _ :: rest ->
         find_in_bucket index rest
    | [] ->
         raise Not_found

(* Get an entry in the table *)
let get table index =
   find_in_bucket index table.(hash table index)
@end[iverbatim]

Finally, the @code{set} function is similar, but it replace an entry in the table, using another
private helper function @code{replace_in_bucket}.

@begin[iverbatim]
(* -- File: table.ml (continued) -- *)
(* Replace an entry in the bucket *)
let rec replace_in_bucket index entry bucket =
   match bucket with
      (index', _) :: rest when index' = index ->
         (index, entry) :: rest
    | head :: rest ->
         head :: replace_in_bucket index entry rest
    | [] ->  (* The entry is new *)
         [(index, entry)]

(* Set the entry *)
let set table index entry =
   let i = hash index in
      table.(i) <- replace_in_bucket index entry table.(i)
@end[iverbatim]

At this point, the signature for the table is fully implemented, and we can move on the the bank
implementation.

@subsection["bank-implementation"]{Bank implementation}

The implementation of the bank is defined in the file @code{bank.ml}.  The first step here is to
give definitions to the types and exceptions in the interface @code{bank.mli}.  These redefinitions
may seem like useless work, but they @emph{must} be defined to satisfy the requirements of the
signature.

@begin[iverbatim]
(* -- File: bank.ml -- *)
(* Accounts are specified by number *)
type account = int

(* Information about an account *)
type account_info = { owner : string; balance : float }

(* Exception for overdrawn accounts *)
exception Overdrawn of account
@end[iverbatim]

To implement the remaining functions, we first create the table for the bank database, and use the
table functions to implement the account operations.  The @code{withdraw} function subtracts the
withdrawn amount, raising an exception if the balance becomes negative, and stores the new entry
otherwise.  The @code{deposit} function has no need for exception handling (although

@begin[iverbatim]
(* Allocate a table *)
let db = ref (Table.create ())

(* Get an account *)
let query account =
   Table.get !db account

(* Withdraw from an account *)
let withdraw_table table account amount =
   let info = Table.get table account in
   let new_balance = info.balance -. amount in

   (* Don't let the balance become negative *)
   if new_balance < 0.0 then
      raise (Overdrawn account);

   (* Add the new entry *)
   let new_info = { info with balance = new_balance } in
      Table.set table account new_info

let withdraw account amount =
   withdraw_from_table !db amount

(* Deposit to an account *)
let deposit account amount =
   withdraw_from_table !db account (-.amount)
@end[iverbatim]

The @code{transaction} function requires a bit more thought.  A simple implementation would iterate
through the list of operations, performing a sequence of transfers.  However, this would not satisfy
the requirement that the @emph{entire} transaction should be abort if any transfer fails.  To
satisfy this requirement, we can copy the table before the transaction, and only commit the copy if
the entire transaction succeeds.

@begin[iverbatim]
let transfer table (from_account, to_account, amount) =
   withdraw_from_table table from_account amount;
   withdraw_from_table table to_account (-.amount)

let transaction transfers =
   let table = Table.copy !db in
      (* An exception may occur during any transfer *)
      List.iter (transfer table) transfers;

      (* All transfers succeeded; commit the result *)
      db := table
@end[iverbatim]

With this definition, the @code{bank.ml} implementation is finished.  The implementation is
functionally correct, but it has a major flaw---the performance of the @code{transaction} function
suffers because the @emph{entire} table is copied on each transaction, even if only a few accounts
are modified.

@subsection["revisiting-the-implementation"]{Revisiting the implementation}

Clearly, our choice of using a hash table is suboptimal for representing accounts.

--- Let's replace the table with a functional one ---

@section[compiling]{Compiling the program}

Once the files for the program are defined, the next step is to
compile them using @tt[ocamlc].  The usage of @tt[ocamlc] is much like
@tt{cc}.  Normally, the files are compiled separately and linked into
an executable.  Signatures must be compiled first, followed by the
implementations.

For the @tt{fset} module, the signature can be compiled with the
following command.

@begin[iverbatim]
% ocamlc -c fset.mli
@end[iverbatim]

If there are no errors in the signature, this step produces a file
called @code{fset.cmi}.

The implementations are compiled with the following command.

@begin[iverbatim]
% ocamlc -c fset.ml
% ocamlc -c test.ml
@end[iverbatim]

If this step is successful, the compiler produces the files
@code{fset.cmo} and @code{test.cmo}.

The modules can now be linked into a complete program using the
@tt[ocamlc] linker.  The command is as follows.

@begin[iverbatim]
% ocamlc -o test fset.cmo test.cmo
@end[iverbatim]

The linker requires all of the @code{.cmo} files to be included in the
program.  The order of these files is important!  Each module in the
link line can refer only to the modules listed @emph{before} it.  If
we reverse the order of the modules on the link line, we will get an
error.

@begin[iverbatim]
% ocamlc -o test test.cmo fset.cmo
Error while linking test.cmo: Reference to undefined global `Fset'
Exit 2
@end[iverbatim]

Once the program is linked, we can run it.

@begin[iverbatim]
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
@end[iverbatim]

@subsection[main]{Where is the main function?}

Unlike C programs, OCaml program do not have a ``@tt{main}''
function.  When an OCaml program is evaluated, all the statements in
the files in the program are evaluated in the order specified on the
link line.  Program files contain type and method definitions.  They
can also contain arbitrary expressions to be evaluated.  The @tt{let
_ = loop ()} statement in the @code["test.ml"] file is an example: it
evaluates the @code{loop} function.  Informally, this is the main
loop; it is the last expression to be executed in the program.

@subsection["common-errors"]{Some common errors}

When a @code[".ml"] file is compiled, the compiler compares the
implementation with the signature in the @code{.cmi} file.  If a
definition does not match the signature, the compiler will print an
error and refuse to compile the file.

@subsubsection["type-mismatch-error"]{Type errors}

For example, suppose we had reversed the order of arguments in the
@code{Fset.insert} function so that the set argument is first.

@begin[iverbatim]
let insert s x =
   ...
@end[iverbatim]

When we compile the file, we get an error.  The compiler prints the
types of the mismatched values, and exits with an error code.

@begin[iverbatim]
% ocamlc -c fset.ml
The implementation fset.ml does not match the interface fset.cmi:
Values do not match:
  val insert : 'a t -> 'a -> 'a t
is not included in
  val insert : 'a -> 'a t -> 'a t
Exit 2
@end[iverbatim]

@subsubsection["missing-def-error"]{Missing definition errors}

Another common error occurs when a method declared in the signature is
not defined in the implementation.  For example, suppose we had
defined an @tt{add} method rather than an @tt{insert} method.  In this
case, the compiler prints the name of the missing method, and exits
with an error code.

@begin[iverbatim]
% ocamlc -c fset.ml
The implementation fset.ml does not match the interface fset.cmi:
The field `insert' is required but not provided
Exit 2
@end[iverbatim]

@subsubsection["type-def-errors"]{Type definition mismatch errors}

@emph{Transparent} type definitions in the signature can also cause an
error if the type definition in the implementation does not match.
Suppose we were to export the definition for @code{type 'a t}.  We
need to include exactly the same definition in the implementation.
A correct @code{fset.mli} file would contain the following definition.

@begin[iverbatim]
type color

type 'a t =
   Node of color * 'a t * 'a * 'a t
 | Leaf
@end[iverbatim]

Note that we must include a type definition for @code{color}, since it
is used in the definition of the set type @code{'a t}.  The type
definition for @code{color} may be transparent or abstract.

Now, suppose we reorder the constructors in the interface definition
for @code{'a t} by placing the @code{Leaf} constructor first.

@begin[iverbatim]
type color

type 'a t =
   Leaf
 | Node of color * 'a t * 'a * 'a t
@end[iverbatim]

When we compile the file, the compiler will produce an error with
the mismatched types.

@begin[iverbatim]
% ocamlc -c fset.mli
% ocamlc -c fset.ml
The implementation fset.ml does not match the interface fset.cmi:
Type declarations do not match:
  type 'a t = | Node of color * 'a t * 'a * 'a t | Leaf
is not included in
  type 'a t = | Leaf | Node of color * 'a t * 'a * 'a t
Exit 2
@end[iverbatim]

@subsubsection["compile-errors"]{Compile dependency errors}

The compiler will also produce errors if the compile state is
inconsistent.  Each time an interface is compile, all the files that
uses that interface must be recompiled.  For example, suppose we
update the @code{fset.mli} file, and recompile it and the
@code{test.ml} file (but we forget to recompile the @code{fset.ml}
file).  The compiler produces the following error.

@begin[iverbatim]
% ocamlc -c fset.mli
% ocamlc -c test.ml
% ocamlc -o test fset.cmo test.cmo
Files test.cmo and fset.cmo make inconsistent
assumptions over interface Fset
Exit 2
@end[iverbatim]

It takes a little work to detect the cause of the error.  The compiler
says that the files make inconsistent assumptions for interface
@code{Fset}.  The interface is defined in the file @code{fset.cmi},
and so this error message states that at least one of @code{fset.ml}
or @code{test.cmo} needs to be recompiled.  In general, we don't know
which file is out of date, and the best solution is to recompile them
all.

@section[open]{Using @tt{open} to expose a namespace}

Using the full name @tt{@emph{Module_name}.@emph{method_name}} to
refer to the methods in a module can get tedious.  The
@tt{open @emph{Module_name}} statement can be used to ``open'' a module
interface, which will allow the use of unqualified names for types,
exceptions, and methods.  For example, the @code{test.ml} module can
be somewhat simplified by using the @code{open} statements for the
@code{Lm_printf} and @code{Fset} modules.

@begin[iverbatim]

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
@end[iverbatim]

Sometimes multiple @tt{open}ed modules will define the same name.  In
this case, the @emph{last} module with an @tt{open} statement will
determine the value of that symbol.  Fully qualified names (of the
form @tt{@emph{Module_name}.@emph{name}}) may still be used even if
the module has been opened.  Fully qualified names can be used to
access values that may have been hidden by an @tt{open} statement.

@subsection["open-errors"]{A note about @tt{open}}

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

@section[debugging]{Debugging a program}

The @code{ocamldebug} program can be used to debug a program compiled
with @code{ocamlc}.  The @code{ocamldebug} program is a little like
the GNU @code{gdb} program; it allows breakpoints to be set.  When a
breakpoint is reached, control is returned to the debugger so that
program variables can be examined.

To use @code{ocamldebug}, the program must be compiled with the
@code{-g} flag.

@begin[iverbatim]
% ocamlc -c -g fset.mli
% ocamlc -c -g fset.ml
% ocamlc -c -g test.ml
% ocamlc -o test -g fset.cmo test.cmo
@end[iverbatim]

The debugger is invoked using by specifying the program to be debugged
on the @code{ocamldebug} command line.

@begin[iverbatim]
% ocamldebug ./test
	Objective Caml Debugger version 2.04

(ocd) help
List of commands :
cd complete pwd directory kill help quit run reverse step
backstep goto finish next start previous print display source
break delete set show info frame backtrace bt up down last
list load_printer install_printer remove_printer

(ocd)
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

For debugging the @code{test} program, we need to know the line
numbers.  Let's set a breakpoint in the @code{loop} function, which
starts in line 27 in the @code{Test} module.  We'll want to stop at
the first line of the function.

@begin[iverbatim]
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
@end[iverbatim]

Next, let's set a breakpoint after the next input line is read and
continue execution to that point.

@begin[iverbatim]
(ocd) list
27 let loop () =
28    let set = ref Fset.empty in
29       <|b|>try
30          while true do
31             output_string stdout "set> ";
32             flush stdout;
33             let line = input_line stdin in
34                if Fset.mem line !set then
35                   Lm_printf.printf "%s is already in the set\n" line
36                else
37                   Lm_printf.printf "%s added to the set\n" line;
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
@end[iverbatim]

When we run the program, the evaluation prompts us for an input line,
and we can see the value of the line in the @code{line} variable.
Let's continue and view the set after the line is added.

@begin[iverbatim]
(ocd) n
Time : 24 - pc : 24628 - module Test
34                if Fset.mem line !set<|a|> then
(ocd) n
Time : 25 - pc : 24672 - module Test
37                   <|b|>Lm_printf.printf "%s added to the set\n" line;
(ocd) n
Time : 135 - pc : 24700 - module Test
37                   Lm_printf.printf "%s added to the set\n" line<|a|>;
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
@end[iverbatim]

This value seems to be correct.  Next, suppose we want to go back a
descend into the @code{Fset.mem} function.  We can go back to time
@code{22} (the time just before the @code{Fset.mem} function is called),
and use the @code{step} command to descend into the membership
function.

@begin[iverbatim]
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
@end[iverbatim]

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

>>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
