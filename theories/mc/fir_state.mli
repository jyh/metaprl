(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * State operations for FIR programs.
 * The state is a pair.  The 2nd component is a list of items in the state.
 *    The 1st component is the length of the list, and also servers
 *    as the next reference id to allocate.  Reference id's start
 *    at zero and increase as you go toward the _beginning_ of the list.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
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
 * Author: Brian Emre Aydemir
 * Email:  emre@its.caltech.edu
 *)

include Base_theory
include Itt_theory

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Triple. *)
declare triple{ 'a; 'b; 'c }

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
declare empty

(*
 * Memory allocation.
 * Allocates a location in state for 'item_list.  Evalutes to a triple:
 *    length of the state after allocation;
 *    modified state;
 *    a reference to the allocated location.
 * This triple should be given to "match" to obtain useful behavior.
 *)
declare alloc{ 'state; 'tag; 'item_list }

(*
 * Assignment.
 * Stores 'item in the 'index-th location of the block at 'ref in 'state.
 *    Returns a triple as in alloc, but the value is it, not a ref, and
 *    the state is not modified.
 *)
declare store{ 'state; 'ref; 'index; 'item }

(*
 * Value lookup.
 * Evaluates to a triple as in alloc, but the state is not modified,
 *    and the value is the value retrieved.
 *)
declare fetch{ 'state; 'ref; 'index }

(*
 * Match / spread.
 * Binds the triple (x,y,z) returned by alloc, store, and fetch
 *    to a <- pair(x,y) and b <- z.
 *)
declare smatch{ 'i; a, b. 'exp['a; 'b] }

(*************************************************************************
 * Rewrites.
 *************************************************************************)

topval reduce_nth_block : conv
topval reduce_replace_nth_block : conv
topval reduce_empty : conv
topval reduce_alloc : conv
topval reduce_store : conv
topval reduce_fetch : conv
topval reduce_smatch : conv
