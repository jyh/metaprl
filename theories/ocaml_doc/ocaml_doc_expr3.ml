doc <:doc< -*- Mode: text -*-

   @begin[spelling]
   btree iff log Okasaki ll deprecated rebalancing
   @end[spelling]

   @begin[doc]
   @chapter[unions]{Unions}
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

   @docoff
>>

extends Base_theory

doc <:doc<
@begin[doc]

Disjoint unions, also called @emph{tagged unions} or @emph{variant
records}, are an important part of the OCaml type system.  A disjoint
union, or union for short, represents the union of several different
types, where each of the cases is given an unique, explicit name.

OCaml allows the definition of @emph{emph} and @emph{open} union
types.  The following syntax is used for an exact union type; we
discuss open types later in this chapter
@refsection["open-union-types"].

@begin[center]
@begin[tabular,l]
@line{{@code{type} @emph{typename} =}}
@line{{$@space$ $@space$ $@emph{Name}_1$ @code{of} $@emph{type}_1$}}
@line{{$@space$ $|$ $@emph{Name}_2$ @code{of} $@emph{type}_2$}}
@line{{$@space$ $@space$ $@vdots$}}
@line{{$@space$ $|$ $@emph{Name}_n$ @code{of} $@emph{type}_n$}}
@end[tabular]
@end[center]

The union type is defined by a set of cases separated by the vertical
bar (@code{|}) character.  Each case $i$ has an explicit name
$@emph{Name}_i$, called a @emph{constructor}; and it has an optional
value of type $@emph{type}_i$.  The constructor name must be
capitalized.  The definition @code{of} $@emph{type}_n$ is optional; if
ommitted there is no explicit value associated with the constructor.

Let's look at a simple example using unions, where we wish to define a
numeric type that is either a value of type @code{int} or @code{float}
or a canonical value @code{Zero}.  We might define this type as follows.

@begin[iverbatim]
# type number =
     Zero
   | Integer of int
   | Real of float;;
type number = Zero | Integer of int | Real of float
@end[iverbatim]

@noindent
Values in a disjoint union are formed by applying a constructor to
an expression of the appropriate type.

@begin[iverbatim]
# let zero = Zero;;
val zero : number = Zero
# let i = Integer 1;;
val i : number = Integer 1
# let x = Real 3.2;;
val x : number = Real 3.2
@end[verbatim]

Patterns also use the constructor name.  For example, we can define a function
that returns a floating-point representation of a number as follows.  In this program,
each pattern specifies a constructor name as well as a variable for the constructors
that have values.

@begin[iverbatim]
# let float_of_number = function
     Zero -> 0.0
   | Integer i -> float_of_int i
   | Real x -> x
@end[iverbatim]

Patterns can be arbitrarily nested.  For example, the following
function represents one way that we might perform addition of values
in the @code{number} type.

@begin[iverbatim]
# let add n1 n2 =
     match n1, n2 with
        Zero, n
      | n, Zero ->
          n
      | Integer i1, Integer i2 ->
          Integer (i1 + i2)
      | Integer i, Real x
      | Real x, Integer i ->
          Real (x +. float_of_int i)
      | Real x1, Real x2 ->
          Real (x1 +. x2);;
val add : number -> number -> number = <fun>
# add x i;;
- : number = Real 4.2
@end[iverbatim]

There are a few things to note in this pattern matching.  First, we are matching
against the pair @code{(n1, n2)} of the numbers @code{n1} and @code{n2} being added.
The patterns are then pair patterns.  For example, the following clause specifies that
if the first number is @code{Zero} and the second is @code{n}, or if the second number
is @code{Zero} and the first is @code{n}, then the sum is @code{n}.

@begin[iverbatim]
        Zero, n
      | n, Zero ->
          n
@end[iverbatim]

The second thing to note is that we are able to collapse some of the
cases using similar patterns.  For example, the code for adding
@code{Integer} and @code{Real} values is the same, whether the first
number is an @code{Integer} or @code{Real}.  In both cases, the
variable @code{i} is bound to the @code{Integer} value, and @code{x}
to the @code{Real} value.

OCaml allows two patterns $p_1$ and $p_2$ to be combined into a choice
pattern $p_1 | p_2$ under two conditions: both patterns must define
the same variables; and, the being matched by multiple occurrences of
a variable must have the same types.  Otherwise, the placement of
variables in $p_1$ and $p_2$ is unrestricted.

In the remainder of this chapter we will describe the the disjoint union
type more completely, using a running example for building balanced binary trees,
a frequently-used data structure in functional programs.

@section["union-binary-trees"]{Binary trees}

Binary trees are frequently used for representing
collections of data.  A binary tree is a collection of nodes (also
called vertices), where each node has either zero or two nodes called
@emph{children}.  If node $n_2$ is a child of $n_1$, then $n_1$ is
called the @emph{parent} of $n_2$.  One node, called the @emph{root},
has no parents; all other nodes have exactly one parent.

One way to represent this data structure is by defining a disjoint
union for the type of a node and its children.  Since each node has
either zero or two children, we need two cases.  The following
definition defines the type for a labeled tree: the @code{'a} type
variable represents the type of labels; the @code{Node} constructor
represents a node with two children; and the @code{Leaf} constructor
represents a node with no children.  Note that the type @code{'a tree}
is defined with a type parameter @code{'a} for the type of labels.
Note that this type definition is recursive.  The type @code{'a tree}
is mentioned in its own definition.

@begin[iverbatim]
# type 'a tree =
     Node of 'a * 'a tree * 'a tree
   | Leaf;;
type 'a tree = | Node of 'a * 'a tree * 'a tree | Leaf
@end[iverbatim]

The use of tuple types in a constructor definition (for example,
@code{Node of 'a * 'a tree * 'a tree}) is quite common, and has an
efficient implementation.  When applying a constructor, parentheses
are required around the elements of the tuple.  In addition, even
though constructors with arguments are similar to functions, they are
not functions, and may not be used as values.

@begin[iverbatim]
# Leaf;;
- : 'a btree = Leaf
# Node (1, Leaf, Leaf);;
- : int btree = Node (1, Leaf, Leaf)
# Node;;
The constructor Node expects 3 argument(s),
but is here applied to 0 argument(s)
@end[iverbatim]

Since the type definition for @code{'a tree} is recursive, many of the functions
defined on the tree will also be recursive.  For example, the following function
defines one way to count the number of non-leaf nodes in the tree.

@begin[iverbatim]
# let rec cardinality = function
     Leaf -> 0
   | Node (_, left, right) ->
        cardinality left + cardinality right + 1;;
val cardinality : 'a btree -> int = <fun>
# cardinality (Node (1, Node (2, Leaf, Leaf), Leaf));;
- : int = 2
@end[iverbatim]

@section["unbalanced-btree"]{Unbalanced binary trees}

Now that we have defined the type if binary trees, lets build a simple
data structure for representing sets of values of type @code{'a}.

The empty set is just a @code{Leaf}.  To add an element to a set @tt{s}, we
create a new @code{Node} with a @code{Leaf} as a left-child, and
@tt{s} as the right child.

@begin[iverbatim]
# let empty = Leaf;;
val empty : 'a btree = Leaf
# let insert x s = Node (x, Leaf, s);;
val insert : 'a -> 'a btree -> 'a btree = <fun>
# let rec set_of_list = function
     [] -> empty
   | x :: l -> insert x (set_of_list l);;
val set_of_list : 'a list -> 'a btree = <fun>
# let s = set_of_list [3; 5; 7; 11; 13];;
val s : int btree =
  Node
   (3, Leaf,
    Node (5, Leaf,
      Node (7, Leaf,
        Node (11, Leaf, Node (13, Leaf, Leaf)))))
@end[iverbatim]

The membership function is defined recursively: an
element $x$ is a member of a tree iff the tree is a @code{Node} and $x$
is the label, or $x$ is in the left or right subtrees.

@begin[iverbatim]
# let rec mem x = function
     Leaf -> false
   | Node (y, left, right) ->
       x = y || mem x left || mem x right;;
val mem : 'a -> 'a btree -> bool = <fun>
# mem 11 s;;
- : bool = true
# mem 12 s;;
- : bool = false
@end[iverbatim]

@section["ordered-btree"]{Unbalanced, ordered, binary trees}

One problem with the unbalanced tree defined here is that the
complexity of the membership operation is $O(n)$, where $n$ is
cardinality of the set.

We can can begin to address the performance by ordering the nodes in
the tree.  The invariant we would like to maintain is the following:
for any interior node @code{Node (x, left, right)}, all the labels in
the left child are smaller than @tt{x}, and all the labels in the
right child are larger than @tt{x}.  To maintain this invariant, we
must modify the insertion function.

@begin[iverbatim]
# let rec insert x = function
     Leaf -> Node (x, Leaf, Leaf)
   | Node (y, left, right) ->
      if x < y then
         Node (y, insert x left, right)
      else if x > y then
         Node (y, left, insert x right)
      else
         Node (y, left, right);;
val insert : 'a -> 'a btree -> 'a btree = <fun>
# let rec set_of_list = function
     [] -> empty
   | x :: l -> insert x (set_of_list l);;
val set_of_list : 'a list -> 'a btree = <fun>
# let s = set_of_list [7; 5; 9; 11; 3];;
val s : int btree =
  Node
   (3, Leaf,
    Node (11,
      Node (9,
        Node (5, Leaf, Node (7, Leaf, Leaf)), Leaf), Leaf))
@end[iverbatim]

Note that this insertion function still does not build balanced trees.
For example, if elements are inserted in increasing order, the tree
will be completely unbalanced, with all the elements inserted along
the right branch.

For the membership function, we can take advantage of
the set ordering to speed up the search.

@begin[iverbatim]
# let rec mem x = function
     Leaf -> false
   | Node (y, left, right) ->
        x = y || (x < y && mem x left) || (x > y && mem y right);;
val mem : 'a -> 'a btree -> bool = <fun>
# mem 5 s;;
- : bool = true
# mem 9 s;;
- : bool = true
# mem 12 s;;
- : bool = false
@end[iverbatim]

The complexity of this membership function is $O(l)$ where $l$ is the
maximal depth of the tree.  Since the @tt{insert} function does not
guarantee balancing, the complexity is still $O(n)$, worst case.

@section["pattern-as"]{Revisiting pattern matching}

The @code{insert} function as expressed above is slightly inefficient.
The final @code{else} clause (containing the expression @code{Node (y,
left, right)}) returns a value that is equal to the one matched, but
the application of the @code{Node} constructor creates a new value.
The code would be more concise, and likely more efficient, if the
matched value were used as the result.

OCaml provides a pattern form for binding the matched value using the
syntax @emph{pattern} @tt[as] @emph{variable}.  In a clause @tt{$p$ as
$v$ -> $e$}, the variable $v$ is a binding occurrence.  When a value
is successfully matched with the pattern $p$, the variable $v$ is
bound to the value during evaluation of the body $e$.  The simplified
@code{insert} function is as follows.

@begin[iverbatim]
# let rec insert x = function
     Leaf -> Node (x, Leaf, Leaf)
   | Node (y, left, right) as node ->
      if x < y then
         Node (y, insert x left, right)
      else if x > y then
         Node (y, left, insert x right)
      else
         node;;
val insert : 'a -> 'a btree -> 'a btree = <fun>
@end[iverbatim]

Patterns with @code{as} bindings may occur anywhere in a pattern.  For
example, the pattern @code{Node (y, left, right)} is equivalent to the
pattern @code{Node (_ as y, (_ as left), (_ as right))}, though the
former is preferred of course.  The parentheses are required because
the @code{as} keyword has very low precedence, lower than comma
(@code{,}) and even the vertical bar (@code{|}).

Another extension to pattern matching is conditional matching with
@code{when} clauses.  The syntax of a conditional match has the form
@emph{pattern} @code{when} @emph{expression}.  The @emph{expression}
is a predicate to be evaluated if the @emph{pattern} matches.  The
variables bound in the pattern may be used in the @emph{expression}.
The match is successful if, and only if, the @emph{expression}
evaluates to true.

A version of the @code{insert} function using @code{when} clauses is
listed below.  When the pattern match is performed, if the value is a
@code{Node}, the second clause @code{Node (y, left, right) when x < y}
is considered.  If $x$ is less than $y$, then $x$ is inserted into the
left branch.  Otherwise, then evaluation falls through the the third
clause @code{Node (y, left, right) when x > y}.  If $x$ is greater
than $y$, then $x$ is inserted into the right branch.  Otherwise,
evaluation falls through to the final clause, which returns the
original node.

@begin[iverbatim]
# let rec insert x = function
     Leaf ->
         Node (x, Leaf, Leaf)
   | Node (y, left, right) when x < y ->
         Node (y, insert x left, right)
   | Node (y, left, right) when x > y ->
         Node (y, left, insert x right)
   | node ->
         node;;
val insert : 'a -> 'a btree -> 'a btree = <fun>
@end[iverbatim]

The performance of this version of the @code{insert} function is
nearly identical to the previous definition using @code{if} to perform
the comparison between $x$ and $y$.  Whether to use @code{when}
conditions is usually a matter of style and preference.

@section["balanced-red-black-trees"]{Balanced red-black trees}

In order to address the performance problem, we turn to an
implementation of balanced binary trees.  We'll use a functional
implementation of red-black trees due to Chris Okasaki @cite[Oka99].
Red-black trees add a label, either @code{Red} or @code{Black}, to each
non-leaf node.  We will establish several new invariants.

@begin[enumerate]
@item{Every leaf is colored black.}
@item{All children of every red node are black.}
@item{Every path from the root to a leaf has the same number of black
nodes as every other path.}
@item{The root is always black.}
@end[enumerate]

These invariants guarantee the balancing.  Since all the children of a
red node are black, and each path from the root to a leaf has the same
number of black nodes, the longest path is at most twice as long as
the shortest path.

The type definitions are similar to the unbalanced binary tree; we
just need to add a red/black label.

@begin[iverbatim]
type color =
   Red
 | Black

type 'a rbtree =
   Node of color * 'a * 'a rbtree * 'a rbtree
 | Leaf
@end[iverbatim]

@noindent
The membership function also has to be redefined for the new type.

@begin[iverbatim]
let rec mem x = function
   Leaf -> false
 | Node (_, y, left, right) ->
      x = y || (x < y && mem x left) || (x > y && mem x right)
@end[iverbatim]

The difficult part of the data structure is maintaining the invariants
when a value is added to the tree with the @tt{insert} function.
This can be done in two parts.  First find the location where
the node is to be inserted.  If possible, add the new node with a
@code{Red} label because this would preserve invariant 3.  This may,
however, violate invariant 2 because the new @tt{Red} node may have a
@tt{Red} parent.

In order to preserve the invariant, we implement the @tt{balance}
function, which considers all the cases where a @tt{Red} node has a
@tt{Red} child and rearranges the tree.

@begin[iverbatim]
# let balance = function
     Black, z, Node (Red, y, Node (Red, x, a, b), c), d
   | Black, z, Node (Red, x, a, Node (Red, y, b, c)), d
   | Black, x, a, Node (Red, z, Node (Red, y, b, c), d)
   | Black, x, a, Node (Red, y, b, Node (Red, z, c, d)) ->
        Node (Red, y, Node (Black, x, a, b), Node (Black, z, c, d))
   | a, b, c, d ->
        Node (a, b, c, d)

  let insert x s =
     let rec ins = function
        Leaf -> Node (Red, x, Leaf, Leaf)
      | Node (color, y, a, b) as s ->
           if x < y then balance (color, y, ins a, b)
           else if x > y then balance (color, y, a, ins b)
           else s
     in
        match ins s with  (* guaranteed to be non-empty *)
           Node (_, y, a, b) -> Node (Black, y, a, b)
         | Leaf -> raise (Invalid_argument "insert");;
val balance : color * 'a * 'a rbtree * 'a rbtree -> 'a rbtree = <fun>
val insert : 'a -> 'a rbtree -> 'a rbtree = <fun>
@end[iverbatim]

Note the use of nested patterns in the @tt{balance} function.  The
@tt{balance} function takes a 4-tuple, with a @tt{color}, two
@tt{btree}s, and an element, and it splits the analysis into five
cases: four of the cases are for the situation where invariant 2 needs
to be re-established because @tt{Red} nodes are nested, and the final
case is the case where the tree does not need rebalancing.

Since the longest path from the root is at most twice as long as the
shortest path, the depth of the tree is $O(log@space n)$.  The
@tt{balance} function takes $O(1)$ (constant) time.  This means that the
@tt{insert} and @tt[mem] functions each take time $O(log@space n)$.

@begin[iverbatim]
# let empty = Leaf;;
val empty : 'a rbtree = Leaf
# let rec set_of_list = function
       [] -> empty
     | x :: l -> insert x (set_of_list l);;
val set_of_list : 'a list -> 'a rbtree = <fun>
# let s = set_of_list [3; 9; 5; 7; 11];;
val s : int rbtree =
  Node (Black, 7, Node (Black, 5, Node (Red, 3, Leaf, Leaf), Leaf),
   Node (Black, 11, Node (Red, 9, Leaf, Leaf), Leaf))
# mem 5 s;;
- : bool = true
# mem 6 s;;
- : bool = false
@end[iverbatim]

@section["open-union-types"]{Open union types}

OCaml defines a second kind of union type where the type is
open---that is, other definitions may add more cases to the type
definition.  The syntax is similar to the exact definition discussed
previously, but the type but the constructor names are prefixed with a
backquote (@code{`}) symbol, and the type definition is enclosed in
@code{[>} $@ldots$ @code{]} brackets.@footnote{As of OCaml 3.08.0, the
language does not allow open union types in type definitions.}

For example, let build an extensible version of the numbers from the first
example in this chapter.  Initially, we might define an @code{add} function
for @code{`Integer} values.

@begin[iverbatim]
# let string_of_number1 n =
     match n with
        `Integer i -> string_of_int i
      | _ -> raise (Invalid_argument "unknown number");;
val string_of_number1 : [> `Integer of int ] -> string = <fun>
# string_of_number1 (`Integer 17);;
- : string = "17"
@end[iverbatim]

The type @code{[> `Integer of int ]} specifies that the function takes
an argument having an open union type, where one of the constructors
is @code{`Integer} (with a value of type @code{int}).

Later, we may come along and want to define a function that includes
a constructor @code{`Real} for floating-point values.  We can extend
the definition as follows.

@begin[iverbatim]
# let string_of_number2 n =
     match n with
        `Real x -> string_of_float x
      | _ -> string_of_number1 n;;
val string_of_number2 : [> `Integer of int | `Real of float ] -> string =
  <fun>
@end[verbatim]

If passed a floating-point number with the @code{`Real} constructor,
the string is created with @code{string_of_float} function.
Otherwise, the original function @code{string_of_number1} is used.

The type @code{[> `Integer of int | `Real of float ]} specifies that
the function takes an argument in an open union type, and handles the
constructors @code{`Integer} with a value of type @code{int}, and
@code{`Real} with a value of type @code{float}.  Unlike the exact
union, the constructors may still be used with expressions of other types.
However, application to a value of the wrong type remains disallowed.

@begin[iverbatim]
# let n = `Real 1;;
val n : [> `Real of int ] = `Real 1
# string_of_number2 n;;
Characters 18-19:
  string_of_number2 n;;
                    ^
This expression has type [> `Real of int ] but is here used with type
  [> `Integer of int | `Real of float ]
Types for tag `Real are incompatible
@end[iverbatim]

@section["common-unions"]{Some common built-in unions}

A few of the types we have already seen are unions.  The built-in
Boolean type @code{bool} is defined as a union.  Normally, the
constructor names in a union must be capitalized.  OCaml defines an
exception in this case by treating @code{true} and @code{false}
as capitalized identifiers.

@begin[iverbatim]
# type bool =
     true
   | false
type bool = | true | false
@end[iverbatim]


The list type is similar, having the following effective definition.
However, the @code{'a list} type is primitive in this case because
@code{[]} is not considered a legal constructor name.

@begin[iverbatim]
type 'a list =
   []
 | :: of 'a * 'a list;;
@end[iverbatim]

Although it is periodically suggested on the OCaml mailing list, OCaml
does not have a NIL value that can be assigned to a variable of
any type.  Instead, the built-in @tt{'a option} type is used.

@begin[iverbatim]
# type 'a option =
     None
   | Some of 'a;;
type 'a option = | None | Some of 'a
@end[iverbatim]

The @tt{None} case is intended to represent a NIL value, while the
@tt{Some} case handles non-NIL values.

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
