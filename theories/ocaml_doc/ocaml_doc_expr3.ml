(*!
 * @begin[spelling]
 * btree iff log mem rebalancing
 * @end[spelling]
 *
 * @begin[doc]
 * @chapter[unions]{Unions}
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
 *
 * @docoff
 *)

extends Base_theory

(*!
@begin[doc]

Disjoint unions, also called @emph{tagged unions} or @emph{variant
records}, are ubiquitous in OCaml programs.  A disjoint union
represents a set of @emph{cases} of a particular type.  For example,
we may say that a binary tree contains nodes that are either
@emph{interior} nodes, or @emph{leaves}.  Suppose that the interior
nodes have a label of type @code{'a}.  In OCaml, this would be
expressed with the following type definition.

@begin[verbatim]
# type 'a btree =
     Node of 'a * 'a btree * 'a btree
   | Leaf;;
type 'a btree = | Node of 'a * 'a btree * 'a btree | Leaf
@end[verbatim]

The cases are separated by a vertical dash (the @code{|} char).  Each
has a name and an optional set of values.  The name must begin with an
uppercase letter.  In this case, the type of the definition is
@code{'a btree}, and the interior node @code{Node} has three values: a
label of type @code{'a}, a left child of type @code{'a btree}, and a
right child of type @code{'a btree}.  The type @code{btree} is
parameterized by the type argument @code{'a}.

The tags (like @code{Node} and @code{Leaf}), are called
@emph{constructors}.  Technically, the constructors can be viewed as
functions that @emph{inject} values into the disjoint union.  Thus,
the @code{Node} constructor would be a function of type
@code{('a * 'a btree * 'a btree) -> 'a btree}.  Note that OCaml does not allow
constructors to be passed as arguments.

@begin[verbatim]
# Leaf;;
- : 'a btree = Leaf
# Node (1, Leaf, Leaf);;
- : int btree = Node (1, Leaf, Leaf)
@end[verbatim]

A value with a union type is a value having @emph{one of} the cases.
The value can be recovered through pattern matching.  For example, a
function that counts the number of interior nodes in a value of type
@code{'a btree} would be defined as follows.

@begin[verbatim]
# let rec cardinality = function
     Leaf -> 0
   | Node (_, left, right) -> cardinality left + cardinality right + 1;;
val cardinality : 'a btree -> int = <fun>
# cardinality (Node (1, Node (2, Leaf, Leaf), Leaf));;
- : int = 2
@end[verbatim]

@section[unbalanced_btree]{Unbalanced binary trees}

To see how this works, lets build a simple data structure for
unbalanced binary trees that represent sets of values of type
@code{'a}.

The empty set is just a @code{Leaf}.  To add an element to a set @tt{s}, we
create a new @code{Node} with a @code{Leaf} as a left-child, and
@tt{s} as the right child.

@begin[verbatim]
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
      Node (7, Leaf, Node (11, Leaf, Node (13, Leaf, Leaf)))))
@end[verbatim]

The membership function is defined by induction on the tree: an
element $x$ is a member of a tree iff the tree is a @code{Node} and $x$
is the label, or $x$ is in the left or right subtrees.

@begin[verbatim]
# let rec mem x = function
     Leaf -> false
   | Node (y, left, right) -> x = y || mem x left || mem x right;;
val mem : 'a -> 'a btree -> bool = <fun>
# mem 11 s;;
- : bool = true
# mem 12 s;;
- : bool = false
@end[verbatim]

@section[ordered_btree]{Unbalanced, ordered, binary trees}

One problem with the unbalanced tree is that the complexity of the
membership operation is $O(n)$, where $n$ is cardinality of the set.
We can improve this slightly by @emph{ordering} the nodes in the tree.
The invariant we maintain is the following: for any interior node
@code{Node (x, left, right)}, all the labels in the left child are
smaller than @tt{x}, and all the labels in the right child are larger
than @tt{x}.  To maintain this invariant, we need to modify the
insertion function.

@begin[verbatim]
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
    Node (11, Node (9, Node (5, Leaf, Node (7, Leaf, Leaf)), Leaf), Leaf))
@end[verbatim]

Note that this insertion function does build balanced trees.  If
elements are inserted in order, the tree will be maximally unbalanced,
with all the elements inserted along the right branch.

For the membership function, we can take advantage of
the set ordering during the search.

@begin[verbatim]
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
@end[verbatim]

The complexity of this membership function is $O(l)$ where $l$ is the
maximal depth of the tree.  Since the @tt{insert} function does not
guarantee balancing, the complexity is still $O(n)$, worst case.

@section[balanced_red_black_trees]{Balanced red-black trees}

To correct the problem with linear complexity, we can use
@emph{balanced} trees.  One common data structure is red-black trees,
which add a label, either @code{Red} or @code{Black} to each of the
interior nodes.  Several new invariants are maintained:

@begin[enumerate]
@item{every leaf is colored black}
@item{all children of every red node are black}
@item{every path from the root to a leaf has the same number of black
nodes as every other path}
@item{the root is always black}
@end[enumerate]

These invariants guarantee the balancing.  Since all the children of a
red node are black, and each path from the root to a leaf has the same
number of black nodes, the longest path is at most twice as long as
the shortest path.

The type definitions are similar to the unbalanced binary tree; we
just need to add a red/black label.

@begin[verbatim]
type color =
   Red
 | Black

type 'a btree =
   Node of color * 'a btree * 'a * 'a btree
 | Leaf
@end[verbatim]

The membership function also has to be redefined for the new type.

@begin[verbatim]
let rec mem x = function
   Leaf -> false
 | Node (_, a, y, b) ->
      if x < y then mem x a
      else if x > y then mem x b
      else true
@end[verbatim]

The @tt{insert} function is made a little more difficult because the
invariants have to be maintained during the insertion.  We can do this
in two parts: first find the location where the node is to be
inserted.  If possible, add the new node with a @code{Red} label
because this would preserve invariant 3.  This may, however, violate
invariant 2 because the new @tt{Red} node may have a @tt{Red} parent.
If this happens, the @tt{balance} function migrates the @tt{Red} label
upward in the tree.

@begin[verbatim]
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
@end[verbatim]

Note the use of nested patterns in the @tt{balance} function.  The
@tt{balance} function takes a 4-tuple, with a @tt{color}, two
@tt{btree}s, and an element, and it splits the analysis into five
cases: four of the cases are for violations of invariant 2 (nested
@tt{Red} nodes), and the final case is the case where the tree does
not need rebalancing.

Since the longest path from the root is at most twice as long as the
shortest path, the depth of the tree is $O(log@space n)$.  The
@tt{balance} function takes constant time.  This means that the
@tt{insert} and @tt{mem} functions both take time $O(log@space n)$.

@begin[verbatim]
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
@end[verbatim]

@section[common_unions]{Some common built-in unions}

A few of the types we have already seen are defined as unions.  The
built-in Boolean type is defined as a union (the @tt{true} and
@tt{false} keywords are treated a capitalized identifiers).

@begin[verbatim]
# type bool =
     true
   | false
type bool = | true | false
@end[verbatim]

The list type is similar: one again, the compiler treats the @code{[]}
and @code{::} identifiers as capitalized identifiers for the scope of
the definition.

@begin[verbatim]
# type 'a list = [] | :: of 'a * 'a list;;
type 'a list = | [] | :: of 'a * 'a list
@end[verbatim]

Although it is periodically suggested on the OCaml mailing list, OCaml
does @emph{not} have a NIL value that can be assigned to a variable of
any type.  Instead, the built-in @tt{'a option} type is used in this case.

@begin[verbatim]
# type 'a option =
     None
   | Some of 'a;;
type 'a option = | None | Some of 'a
@end[verbatim]

The @tt{None} case is intended to represent a NIL value, while the
@tt{Some} case handles non-default values.

@end[doc]

@docoff
*)

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
