(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * State operations for FIR programs.
 *)

include Base_theory
include Fir_sos

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * First location.
 * Refers to the first memory location in the state.
 *)
declare first

(*
 * Next location.
 * Refers to the next memory location after 'loc in the state.
 *)
declare next{ 'loc }

(*
 * Location equality.
 * Tests to see if 'loc1 and 'loc2 are the same location.  Evaluates
 *    to 'e1 if they are the same, and 'e2 otherwise.
 *)
declare if_eq_loc{ 'loc1; 'loc2; 'e1; 'e2 }

(*
 * Pointer.
 * Refers to a memory location. Not actually a location or the
 *    contents of a location.
 *)
declare pointer{ 'loc }

(*
 * Empty state.
 * The program state that contains nothing.
 *)
declare empty

(*
 * Memory allocation.
 * Allocation a spot for 'item in 'state and assign 'item to that new
 *    location.  Evaluates to a pair of the new state and the location
 *    of where the item was stored.
 *)
declare alloc{ 'state; 'item }

(*
 * Assignment.
 * Assign the location 'loc in 'state the value 'item, assuming
 *    that 'loc is an already allocated location.  Evaluates to a pair
 *    of dot (the non-value value) and the updated state.
 *)
declare store{ 'state; 'loc; 'item }

(*
 * Value lookup.
 * Retrieve the value at 'loc in 'state. Evaluates to a pair of
 *    the value retrieved and the state (which is unchanged by
 *    the lookup).
 *)
declare fetch{ 'state; 'loc }
