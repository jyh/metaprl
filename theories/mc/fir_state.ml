(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * State operations for FIR programs.
 * The state is a pair.  The 2nd component is a list of items in the state.
 *    The 1st component is the length of the list, and also servers
 *    as the next reference id to allocate.  Reference id's start
 *    at zero and increase as you go toward the _beginning_ of the list.
 * This file may be removed at a later date if its contents continue
 *    to serve little purpose.
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

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Triple. *)
declare triple{ 'a; 'b; 'c }

(* Blocks / memory. *)
declare block{ 'tag; 'args }

(* Block indexing. *)
declare nth_block{ 'block; 'index }

(* Replacing block elements. *)
declare replace_nth_block{ 'block; 'index; 'item_list }

(* Reference. *)
declare ref{ 'num }

(* Empty state. *)
declare empty

(* Memory allocation. *)
declare alloc{ 'state; 'tag; 'item_list }

(* Assignment. *)
declare store{ 'state; 'ref; 'index; 'item }

(* Value lookup. *)
declare fetch{ 'state; 'ref; 'index }

(* Match / spread. *)
declare smatch{ 'i; a, b. 'exp['a; 'b] }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Triple. *)
dform triple_df : except_mode[src] :: triple{ 'a; 'b; 'c } =
   `"(" slot{'a} `", " slot{'b} `", " slot{'c} `")"

(* Blocks / memory. *)
dform block_df : except_mode[src] :: block{ 'tag; 'args } =
   `"block(" slot{'tag} `", " slot{'args} `")"

(* Block indexing. *)
dform nth_block_df : except_mode[src] :: nth_block{ 'block; 'index } =
   `"nth_block(" slot{'block} `", " slot{'index} `")"

(* Replacing block elements. *)
dform replace_nth_block_df : except_mode[src] ::
   replace_nth_block{ 'block; 'index; 'item_list } =
   `"replace_nth_block(" slot{'block} `", " slot{'index} `", "
   slot{'item_list} `")"

(* Reference. *)
dform ref_df : except_mode[src] :: ref{ 'num } =
   `"ref(" slot{'num} `")"

(* Empty state. *)
dform empty_df : except_mode[src] :: empty =
   `"empty"

(* Memory allocation. *)
dform alloc_df : except_mode[src] :: alloc{ 'state; 'tag; 'item_list } =
   `"alloc(" slot{'state} `", " slot{'tag} `", " slot{'item_list} `")"

(* Assignment. *)
dform store_df : except_mode[src] :: store{ 'state; 'ref; 'index; 'item } =
   `"store(" slot{'state} `", " slot{'ref} `"[" slot{'index} `"], "
   slot{'item} `")"

(* Value lookup. *)
dform fetch_df : except_mode[src] :: fetch{ 'state; 'ref; 'index} =
   `"fetch(" slot{'state} `", " slot{'ref} `"[" slot{'index} `"])"

(* Match / spread. *)
dform smatch_df : except_mode[src] :: smatch{'x; a, b. 'body} =
   szone pushm[0] push_indent `"let <" slot{'a} `"," slot{'b} `"> =" hspace
   szone slot{'x} ezone popm hspace
   push_indent `"in" hspace
   szone slot{'body} ezone popm
   ezone popm

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Block indexing. *)
prim_rw reduce_nth_block :
   nth_block{ block{ 't; 'args }; 'index } <-->
   nth{ 'args; 'index }

(* Replacing block elements. *)
prim_rw reduce_replace_nth_block :
   replace_nth_block{ block{'tag; 'args}; 'index; 'item_list } <-->
   block{ 'tag; replace_nth{ 'args; 'index; 'item_list } }

(* Empty state. *)
prim_rw reduce_empty : empty <--> pair{ 0; nil }

(*
 * Memory allocation.
 * Generate new reference id's using the current length of the state.
 *)
prim_rw reduce_alloc :
   alloc{ pair{ 'num; 's }; 'tag; 'item_list } <-->
   triple{ ('num +@ 1);
      cons{ block{'tag; 'item_list}; 's };
      ref{ 'num } }

(*
 * Assignment.
 * We go through the state list, locate the block to replace in,
 *    replace the one element in it, and then cons on the remainder of
 *    the list.
 *)
prim_rw reduce_store :
   store{ pair{ 'num; 's }; ref{'n}; 'index; 'item_list } <-->
   triple{
      'num;
      (list_ind{ 's; nil; h, t, f.
         lambda{ x. ifthenelse{ beq_int{'x; 0};
            cons{ replace_nth_block{ 'h; 'index; 'item_list }; 't };
            cons{ 'h; .'f ('x -@ 1)}}}} (('num -@ 1) -@ 'n) );
      it }

(*
 * Value lookup.
 * Fetching a value doesn't modify the state.
 *)
prim_rw reduce_fetch :
   fetch{ pair{ 'num; 's }; ref{'n}; 'index } <-->
   triple{ 'num; 's; nth_block{
      nth{ 's; ( ( 'num -@ 1 ) -@ 'n ) };
      'index } }

(* Match / spread. *)
prim_rw reduce_smatch :
   smatch{ triple{ 'x; 'y; 'z }; a, b. 'exp[ 'a; 'b ] } <-->
   'exp[ pair{ 'x; 'y }; 'z ]

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << nth_block{ block{ 't; 'args }; 'index } >>, reduce_nth_block;
   << replace_nth_block{ block{'tag; 'args}; 'index; 'item_list } >>,
      reduce_replace_nth_block;
   << empty >>, reduce_empty;
   << alloc{ 'state; 'tag; 'item_list } >>, reduce_alloc;
   << store{ 'state; 'ref; 'index; 'item_list } >>, reduce_store;
   << fetch{ 'state; 'ref; 'index } >>, reduce_fetch;
   << smatch{ 'i; a, b. 'exp['a; 'b] } >>, reduce_smatch
]
