(*
 * Print terms as strings.
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

open Ml_print_sig
open Ml_print

(*
 * Show the file loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Ml_string%t" eflush

(*
 * String printer.
 *)
module StringFile =
struct
   type t = { mutable buf : string list }
   type name = unit
   type out = string

   (*
    * Creation.
    *)
   let create () = { buf = [] }
   let close _ = ()

   (*
    * Printing.
    *)
   let puti _ _ = ()
   let put file s =
      file.buf <- s :: file.buf

   let get { buf = buf } =
      let rec count i = function
         h::t ->
            count (i + String.length h) t
       | [] ->
            i
      in
      let length = count 0 buf in
      let out = String_util.create "Ml_string.get" length in
      let rec squash i = function
         h::t ->
            let len = String.length h in
            let off = i - len in
               String_util.blit "Ml_string.get" h 0 out off len;
               squash off t
       | [] ->
            ()
      in
         squash length buf;
         out
end

(*
 * Printer.
 *)
module StringPrint = MakePrinter (StringFile)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
