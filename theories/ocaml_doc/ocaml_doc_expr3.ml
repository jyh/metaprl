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
types, where each of the cases is given an unique, explicit name.  The
following syntax is used for defining a union type.

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
Values in a disjoint union are constructed by applying a constructor to
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
pattern $p_1 | p_2$ under two conditions: both patterns must
define the same variables; and, the variables must have the same
types.  Otherwise, the placement of variables in $p_1$ and $p_2$ is
unrestricted.

In the remainder of this chapter we will describe the the disjoint union
type more completely, using a running example for building balanced binary trees,
and frequently-used data structure in functional programs.

@section["union-binary-trees"]{Binary trees}

Binary trees are frequently used data structure for representing
collection of data.  A binary tree is a collection of nodes (also
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

One problem with the unbalanced tree is that the complexity of the
membership operation is $O(n)$, where $n$ is cardinality of the set.

We can can begin to address this by ordering the nodes in the tree.
The invariant we would like to maintain is the following: for any
interior node @code{Node (x, left, right)}, all the labels in the left
child are smaller than @tt{x}, and all the labels in the right child
are larger than @tt{x}.  To maintain this invariant, we need to modify
the insertion function.

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

Note that this insertion function still does not build balanced trees.  If
elements are inserted in order, the tree will be maximally unbalanced,
with all the elements inserted along the right branch.

For the membership function, we can take advantage of
the set ordering during the search.

@begin[iverbatim]
# let rec mem x = function
     Leaf -> false
   | Node (y, left, right) ->
        if x < y then
           mem x left
        else if x > y then
           mem x right
        else (* x = y *)
           true;;
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

@section["balanced-red-black-trees"]{Balanced red-black trees}

In order to address the complexity problem, we turn to an
implementation of balanced binary trees.  We'll use a functional
implementation of red-black trees due to Chris Okasaki @cite[Oka99].
Red-black trees add a label, either @code{Red} or @code{Black}, to each
of the interior nodes.  We will establish several new invariants.

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

type 'a btree =
   Node of color * 'a btree * 'a * 'a btree
 | Leaf
@end[iverbatim]

The membership function also has to be redefined for the new type.

@begin[iverbatim]
let rec mem x = function
   Leaf -> false
 | Node (_, a, y, b) ->
      if x < y then mem x a
      else if x > y then mem x b
      else true
@end[iverbatim]

The @tt{insert} function must maintain the invariants during
insertion.  This can be done in two parts.  First find the location where
the node is to be inserted.  If possible, add the new node with a
@code{Red} label because this would preserve invariant 3.  This may,
however, violate invariant 2 because the new @tt{Red} node may have a
@tt{Red} parent.  If this happens, the @tt{balance} function migrates
the @tt{Red} label upward in the tree.

@begin[iverbatim]
# let balance = function
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
         | Leaf -> raise (Invalid_argument "insert");;
val balance : color * 'a btree * 'a * 'a btree -> 'a btree = <fun>
val insert : 'a -> 'a btree -> 'a btree = <fun>
@end[iverbatim]

Note the use of nested patterns in the @tt{balance} function.  The
@tt{balance} function takes a 4-tuple, with a @tt{color}, two
@tt{btree}s, and an element, and it splits the analysis into five
cases: four of the cases are for violations of invariant 2 (nested
@tt{Red} nodes), and the final case is the case where the tree does
not need rebalancing.

Since the longest path from the root is at most twice as long as the
shortest path, the depth of the tree is $O(log@space n)$.  The
@tt{balance} function takes constant time.  This means that the
@tt{insert} and @tt[mem] functions both take time $O(log@space n)$.

@begin[iverbatim]
# let empty = Leaf;;
val empty : 'a btree = Leaf
# let rec set_of_list = function
     [] -> empty
   | x :: l -> insert x (set_of_list l);;
val set_of_list : 'a list -> 'a btree = <fun>
# let s = set_of_list [3; 9; 5; 7; 11];;
val s : int btree =
  Node
   (Black, Node (Black, Node (Red, Leaf, 3, Leaf), 5, Leaf), 7,
    Node (Black, Node (Red, Leaf, 9, Leaf), 11, Leaf))
# mem 5 s;;
- : bool = true
# mem 6 s;;
- : bool = false
@end[iverbatim]

@section["common-unions"]{Some common built-in unions}

A few of the types we have already seen are defined as unions.  The
built-in Boolean type is defined as a union (the @tt{true} and
@tt{false} keywords are treated as capitalized identifiers).

@begin[iverbatim]
# type bool =
     true
   | false
type bool = | true | false
@end[iverbatim]

The list type is similar: once again, the compiler treats the
@code{[]} and @code{::} identifiers as capitalized
identifiers@begin[footnote]
At the time of writing using OCaml 2.04,
this definition was accepted literally.  In OCaml 3.04 this usage is
deprecated, and the [] produces a syntax error.
@end[footnote].

@begin[iverbatim]
# type 'a list = [] | :: of 'a * 'a list;;
type 'a list = | [] | :: of 'a * 'a list
@end[iverbatim]

Although it is periodically suggested on the OCaml mailing list, OCaml
does @emph{not} have a NIL value that can be assigned to a variable of
any type.  Instead, the built-in @tt{'a option} type is used in this case.

@begin[iverbatim]
# type 'a option =
     None
   | Some of 'a;;
type 'a option = | None | Some of 'a
@end[iverbatim]

The @tt{None} case is intended to represent a NIL value, while the
@tt{Some} case handles non-default values.

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
