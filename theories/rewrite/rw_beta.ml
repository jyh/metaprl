(*
 * Rewriting tool.
 * This just tests out a beta reduction.
 *)

open Printf

open Debug
open Refiner.Refiner.Term
open Dform_print
open Refine
open Refiner

include Itt_theory

(*
 * Here's the term we want to reduce.
 *)
let t = << (lambda{x. 'x +@ 'x} 2) -> 1 >>

(*
(*
 * Copy to the library.
 *)
let library_copy t =
   (*
    * Open library connection.
    *)
   let connect = Library.connect "alfheim" 7401 7400 in
   let library = Library.lib_open connect in
       
   (*
    * Save the term.
    *)
   let save trans =
      let id = Library.create trans "TERM" None [] in
         Library.put_term trans id t;
         id
   in
   let id = Library.with_transaction library save in
       
   (*
    * Retrieve the same term.
    *)
   let restore trans =
      Library.get_term trans id
   in
   let t' = Library.with_transaction library restore in
      if t = t' then
         eprintf "Terms are equal%t" eflush
      else
         eprintf "Terms are not equal!%t" eflush;
      Library.lib_close library;
      Library.disconnect connect;
      t'
*)
       
(*
 * Main function
 *)
let main () =
   (*
    * Now perform the reduction.
    *)
   let rw = rwaddr (make_address [0]) betaReduction in
   let tac = rwtactic rw in
   let t' =
      match refine tac (t, ()) with
         [t, _], _ -> t
       | _ -> raise (Failure "Rw_beta: rewrite failed")
   in
      print_term t;
      eflush stdout

let _ = Printexc.catch main ()

(*
 * $Log$
 * Revision 1.3  1998/05/28 13:48:30  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.2  1997/09/08 15:02:40  jyh
 * This version compiles Ensemble.
 *
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
