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

(* Replace association list elements. *)
declare replace_nth_assoc{ 'eq; 'key; 'l; 'item }

(* Blocks / memory. *)
declare block{ 'tag; 'args }

(* Block indexing. *)
declare nth_block{ 'block; 'index }

(* Replacing block elements. *)
declare replace_nth_block{ 'block; 'index; 'item_list }

(* Reference. *)
declare ref{ 'num }

(* Empty state. *)
define unfold_empty : empty <--> nil

(* Memory allocation. *)
declare alloc{ 'state; 'tag; 'item_list }

(* Assignment. *)
declare store{ 'state; 'ref; 'index; 'item }

(* Value lookup. *)
declare fetch{ 'state; 'ref; 'index }

(* Block lookup. *)
declare fetch_block{ 'state; 'ref }

(* Match / spread. *)
define unfold_match :
   "match"{ 'i; a, b. 'exp['a; 'b] } <-->
   spread{ 'i; a, b. 'exp['a; 'b] }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Replace association list elements. *)
dform replace_nth_assoc_df : except_mode[src] ::
   replace_nth_assoc{ 'eq; 'key; 'l; 'item } =
   `"replace_nth_assoc(" slot{'eq} `", " slot{'key} `", "
   slot{'l} `", " slot{'item} `")"

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
   `"[]"

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

(* Block lookup. *)
dform fetch_block_df : except_mode[src] :: fetch_block{ 'state; 'ref } =
   `"fetch_block(" slot{'state} `", " slot{'ref} `")"

(* Match / spread. *)
dform match_df : except_mode[src] :: "match"{'x; a, b. 'body} =
   szone pushm[0] push_indent `"let <" slot{'a} `"," slot{'b} `"> =" hspace
   szone slot{'x} ezone popm hspace
   push_indent `"in" hspace
   szone slot{'body} ezone popm
   ezone popm

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Replace association list elements. *)
prim_rw reduce_replace_nth_assoc :
   replace_nth_assoc{ 'eq; 'key; 'l; 'item } <-->
   list_ind{ 'l; nil; h, t, f.
      ifthenelse{ ('eq 'key fst{'h});
         cons{ pair{'key; 'item}; 'f };
         cons{ 'h; 'f } } }

(* Block indexing. *)
prim_rw reduce_nth_block :
   nth_block{ block{ 't; 'args }; 'index } <-->
   nth{ 'args; 'index }

(* Replacing block elements. *)
prim_rw reduce_replace_nth_block :
   replace_nth_block{ block{'tag; 'args}; 'index; 'item_list } <-->
   block{ 'tag; replace_nth{ 'args; 'index; 'item_list } }

(*
 * Memory allocation.
 * Generate new reference id's using the current length of the state.
 *)
prim_rw reduce_alloc :
   alloc{ 'state; 'tag; 'item_list } <-->
   pair{ cons{ pair{length{'state}; block{'tag; 'item_list}}; 'state };
         ref{length{'state}} }

(*
 * Assignment.
 *)
prim_rw reduce_store :
   store{ 'state; ref{'n}; 'index; 'item_list } <-->
   "match"{ fetch_block{ 'state; ref{'n} }; s2, v. pair{
      replace_nth_assoc{
         lambda{a. lambda{b. beq_int{'a; 'b}}};
         'n;
         's2;
         replace_nth_block{ 'v; 'index; 'item_list } };
      it} }

(*
 * Value lookup.
 * Fetching a value doesn't modify the state.
 *)
prim_rw reduce_fetch :
   fetch{ 'state; ref{'n}; 'index } <-->
   pair{ 'state; nth_block{
      assoc{ lambda{a. lambda{b. beq_int{'a; 'b}}}; 'n; 'state; x. 'x; it };
      'index } }

(*
 * Block lookup.
 * Similar to fetching a value. We just don't index the block.
 *)
prim_rw reduce_fetch_block :
   fetch_block{ 'state; ref{'n} } <-->
   pair{ 'state;
      assoc{ lambda{a. lambda{b. beq_int{'a; 'b}}}; 'n; 'state; x. 'x; it } }

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << replace_nth_assoc{ 'eq; 'key; 'l; 'item } >>,
      reduce_replace_nth_assoc;
   <<  nth_block{ block{ 't; 'args }; 'index } >>, reduce_nth_block;
   << replace_nth_block{ block{'tag; 'args}; 'index; 'item_list } >>,
      reduce_replace_nth_block;
   << empty >>, unfold_empty;
   << alloc{ 'state; 'tag; 'item_list } >>, reduce_alloc;
   << store{ 'state; 'ref; 'index; 'item_list } >>, reduce_store;
   << fetch{ 'state; 'ref; 'index } >>, reduce_fetch;
   << fetch_block{ 'state; ref{'n} } >>, reduce_fetch_block;
   << "match"{ 'i; a, b. 'exp['a; 'b] } >>, unfold_match
]
