(*
 * Build the toploop version.
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
open Mp_debug

let _ =
   if !debug_load then
      eprintf "Loading Mp_top%t" eflush

module Shell = Shell.Shell (Shell_mp.ShellP4 (Shell_state.ShellState))

let _ =
   if !debug_load then
      eprintf "Loaded Shell%t" eflush

module ShellHTTP = Shell_http.ShellHTTP (Shell)

let _ =
   if !debug_load then
      eprintf "Starting main loop%t" eflush

let _ = ShellHTTP.main ()

external exit : int -> unit = "caml_exit"

let _ =
   eprintf "MetaPRL exiting%t" eflush;
   flush stdout;
   exit 0

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
