(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * State operations for FIR programs.
 * I'll represent the state as an association list keyed
 *    on non-negative integers.  I also assume that in this association
 *    list, the only values are blocks.
 *)

include Base_theory
include Itt_theory

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Replace association list elements.
 * Replace the item in the association list 'l keyed by 'key
 *    (as determined by 'eq) with 'item.  Amounts to a fancy no-op
 *    if an keyed by 'key can't be found in the list.
 *)
declare replace_nth_assoc{ 'eq; 'key; 'l; 'item }

(*
 * Memory is allocated in blocks.
 * Each block has a tag and some values (a list).
 *)
declare block{ 'tag; 'args }

(*
 * Block indexing.
 * Retrieve the 'index-th item in a block.
 *)
declare nth_block{ 'block; 'index }

(*
 * Replacing block elements.
 * Replaces the 'index-th element in the block with 'item_list.
 *)
declare replace_nth_block{ 'block; 'index; 'item_list }

(*
 * Reference.
 * Refers to a memory location.  'loc will be an index
 *    into a list of items in the state.
 *)
declare ref{ 'num }

(*
 * Empty state.
 * The program state that contains nothing.
 *)
define unfold_empty : empty <--> nil

(*
 * Memory allocation.
 * Allocates a location in state for 'item_list.  Evaluates to a pair
 *    which is the new state and a reference to the location used.
 *)
declare alloc{ 'state; 'tag; 'item_list }

(*
 * Assignment.
 * Stores 'item in the 'index-th location of the block at 'ref in 'state.
 *    Evaluates to a pair which is the state and it.
 *)
declare store{ 'state; 'ref; 'index; 'item }

(*
 * Value lookup.
 * Evaulates to a pair which is the state and the value at the 'index-th
 *    location in the block at 'ref.  The value will be it if the reference
 *    or index is invalid.
 *)
declare fetch{ 'state; 'ref; 'index }

(*
 * Block lookup.
 * Return the block referred to by 'ref.
 *)
declare fetch_block{ 'state; 'ref }

(*
 * Match / spread.
 * Declared here for convinience (so I claim) in working with the above.
 *)
define unfold_match :
   "match"{ 'i; a, b. 'exp['a; 'b] } <-->
   spread{ 'i; a, b. 'exp['a; 'b] }
