(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * State operations for FIR programs.
 *)

include Base_theory

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* First allocated location. *)
declare first

(* Next location. *)
declare next{ 'loc }

(* Location equality. *)
declare if_eq_loc{ 'loc1; 'loc2; 'e1; 'e2 }

(* Pointer. *)
declare pointer{ 'loc }

(* Empty state. *)
declare empty

(* Memory allocation. *)
declare alloc{ 'state; 'item }

(* Assignment. *)
declare store{ 'state; 'loc; 'item }

(* Value lookup. *)
declare fetch{ 'state; 'loc }

(*************************************************************************
 * Display forms.
 *************************************************************************)

dform first_df : except_mode[src] :: first =
   `"first"

dform next_df : except_mode[src] :: next{ 'loc } =
   `"next(" slot{'loc} `")"

dform if_eq_loc_df : except_mode[src] :: if_eq_loc{ 'loc1; 'loc2; 'e1; 'e2 } =
   pushm[0] szone push_indent `"if " slot{'loc1} `"=" slot{'loc2}
      `" then" hspace
   szone slot{'e1} ezone popm hspace
   push_indent `"else" hspace
   szone slot{'e2} ezone popm
   ezone popm

dform empty_df : except_mode[src] :: empty =
   `"[]"

dform alloc_df : except_mode[src] :: alloc{ 'state; 'item } =
   `"alloc(" slot{'state} `", " slot{'item} `")"

dform store_df : except_mode[src] :: store{ 'state; 'loc; 'item } =
   `"store(" slot{'state} `", " slot{'loc} `", " slot{'item} `")"

dform fetch_df : except_mode[src] :: fetch{ 'state; 'loc } =
   `"fetch(" slot{'state} `", " slot{'loc} `")"

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Location equality. *)
prim_rw reduce_if_eq_loc1 :
   if_eq_loc{ first; first; 'e1; 'e2 } <--> 'e1
prim_rw reduce_if_eq_loc2 :
   if_eq_loc{ next{ 'loc }; first; 'e1; 'e2 } <--> 'e2
prim_rw reduce_if_eq_loc3 :
   if_eq_loc{ first; next{ 'loc }; 'e1; 'e2 } <--> 'e2
prim_rw reduce_if_eq_loc4 :
   if_eq_loc{ next{ 'loc1 }; next{ 'loc2 }; 'e1; 'e2 } <-->
   if_eq_loc{ 'loc1; 'loc2; 'e1; 'e2 }

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << if_eq_loc{ first; first; 'e1; 'e2 } >>, reduce_if_eq_loc1;
   << if_eq_loc{ next{ 'loc }; first; 'e1; 'e2 } >>, reduce_if_eq_loc2;
   << if_eq_loc{ first; next{ 'loc }; 'e1; 'e2 } >>, reduce_if_eq_loc3;
   << if_eq_loc{ next{ 'loc1 }; next{ 'loc2 }; 'e1; 'e2 } >>, reduce_if_eq_loc4
]
