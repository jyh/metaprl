(*
 * This is a forward-chaining cache, based on sequents.
 * Initially the cache is constructed from a list of rules
 * about forward chaining.  The rules specify how to
 * deduce new facts from old ones.
 *)

open Refiner.Refiner.Term

(*
 * The cache is initially constructed as a "fcache" from a collection of rules.
 * During refinement, this is compiled to a "extract", which propagates
 * inherited attributes down the tree.  After refinement, the synthesized
 * attributes are computed using "fsynthesis".
 *)
type 'a cache
type 'a extract
type 'a synthesis

(*
 * A forward-chaining rule.
 * The justification (which is probably going to be a tactic),
 * takes the indices of the hyps as arguments, takes
 * the names of the results, and produces an 'a (which is
 * probably a tactic).
 *)
type 'a frule =
   { fc_ants : term list;
     fc_concl : term list;
     fc_just : 'a
   }

(*
 * Similar back-chaining rule.
 *)
type 'a brule =
   { bc_concl : term;
     bc_ants : (term list * term) list;
     bc_just : 'a
   }

(*
 * A proof has a forward and a backward component.
 *)
type 'a proof =
   ForeTactics of (int list * 'a) list
 | BackTactic of ('a * 'a proof list)
 | NthHyp of int
 | SeqTactic of 'a proof list

(*
 * Build up the cache.
 * The argument is a justification composition
 * function.
 *)
val new_cache : unit -> 'a cache
val join_cache : 'a cache -> 'a cache -> 'a cache
val add_frule : 'a cache -> 'a frule -> 'a cache
val add_brule : 'a cache -> 'a brule -> 'a cache
val extract : 'a cache -> 'a extract

(*
 * Cache operations.
 *)
val add_hyp : 'a extract -> int -> string -> term -> 'a extract
val del_hyp : 'a extract -> int -> 'a extract
val ref_hyp : 'a extract -> int -> 'a extract
val name_hyp : 'a extract -> int -> string -> 'a extract
val set_goal : 'a extract -> term -> 'a extract

(*
 * Queries.
 *)
val chain : 'a extract -> bool
val lookup : 'a extract -> 'a proof

(* Synthesized attributes *)
val synthesize : 'a extract -> 'a synthesis list -> 'a synthesis
val used_hyps : 'a synthesis -> int list

(*
 * $Log$
 * Revision 1.4  1998/06/01 13:57:06  jyh
 * Proving twice one is two.
 *
 * Revision 1.3  1998/05/28 13:48:38  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.2  1998/05/07 16:03:11  jyh
 * Adding interactive proofs.
 *
 * Revision 1.1  1997/04/28 15:52:43  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.4  1996/11/13 22:58:44  jyh
 * Initial version of forward/backward chaining cache.
 *
 * Revision 1.3  1996/11/05 02:42:41  jyh
 * This is a version of the FCache with complete forward chaining,
 * and multiple worlds.  Untested.
 *
 * Revision 1.2  1996/11/01 01:25:17  jyh
 * This is version of the cache for pur forward chaining.
 * Right now, I am thinking about extending the chainer with "worlds,"
 * which will be necessary to incorporate backward chaining.
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
