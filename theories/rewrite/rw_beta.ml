(*
 * Rewriting tool.
 * This just tests out a beta reduction.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

open Printf

open Nl_debug
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
 * -*-
 * Local Variables:
 * Caml-master: "rw.run"
 * End:
 * -*-
 *)
