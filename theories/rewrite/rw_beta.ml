(*
 * Rewriting tool.
 *)

open Debug
open Term
open Dform_print
open Refine
open Refiner

include Itt_theory

(*
 * Try out a simple reduction.
 *)
let t =
   let rw = rwaddr (make_address [0]) betaReduction in
   let tac = rwtactic rw in
   let t = << (lambda{x. 'x +@ 'x} 2) -> 1 >> in
      match refine tac (t, ()) with
         [t, _], _ -> t
       | _ -> raise (Failure "Rw_beta: rewrite failed")

(*
 * Sorry about this code.
 * I'm working on a more general printing mechanism.
 *)
let _ =
   print_term t;
   eflush stdout

(*
 * $Log$
 * Revision 1.1  1997/08/06 16:18:53  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "rw.run"
 * End:
 * -*-
 *)
