(*
 * Create tables for success/failure/cycle-detection
 * caches.
 *)

open Refiner.Refiner.TermType

(*
 * Compare two terms, given a set of constants.
 *)
val sort_term_list : term list -> term list
val merge_term_lists : term list -> term list -> term list

module TptpCache :
sig
   (*
    * Type of caches.
    *)
   type t

   (*
    * The strings are the function and predicate symbols in
    * the logic.
    *)
   val create : string list -> t

   (*
    * A clause is "subsumed" when an existing entry is
    * found that has a subset of the clause in the
    * argument.
    *)
   val subsumed : t -> term list -> bool

   (*
    * Add a new clause to the table.
    * This is functional, and it is assumed
    * that the clause is not already in the
    * table.  This operation is functional.
    *)
   val insert : t -> term list -> t
end

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
