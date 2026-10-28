(*
 * Main function collects arguments, and starts parsing.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
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
open Arg
open Printf

open Lm_debug

open Filter_parse

(*
 * Show the file loading.
 *)
let _ =
   show_loading "Loading Filter_main%t"

(*
 * string -> path commands
 *)
(* MP_INCLUDE (mk/prlcomp) is a list of directories joined with the
   platform's path-list separator: ";" on Windows, where a directory
   name can contain ":" (d:\...), and ":" elsewhere. *)
let set_path doc var path =
   let sep = if Sys.os_type = "Win32" then ";" else ":" in
   let path' = Lm_string_util.split sep path in
      var := path'

let set_path_arg doc var =
   Arg.String (set_path doc var)

(*
 * This is a list of hosts to use for database lookup.
 *)
let include_path = Env_arg.general "include" ["."] "Include directories" set_path set_path_arg

let add_include path =
   include_path := !include_path @ [path]

let set_output_file name =
   Pcaml.output_file := Some name

let remove_output_file () =
   match !Pcaml.output_file with
      Some name ->
         Sys.remove name
    | None ->
         ()

let set_lib s =
   let var = sprintf "MPLIB=%s" s in
      Punix.putenv var

let set_export () =
   Punix.putenv "MP_EXPORT=true"

let add_anon_arg arg =
   Filter_util.source_file := arg;
   Plexing.input_file := arg;
   Pcaml.input_file := arg

let spec =
   ["-I", String add_include, "add a directory to the path for include files";
    "-o", String set_output_file, "specify output file";
    "-lib", String set_lib, "specify MPLIB directory";
    "-export", Unit set_export, "export an ASCII file"]

(*
 * This program is camlp5 with the MetaPRL filter linked in, and camlp5's
 * odyl.cmo is its main module: it runs camlp5's Main.go, which parses the
 * command line and preprocesses the file. camlp5 7 and 8 install no
 * odyl_main.cmi, so this file cannot call Odyl_main.go itself.
 *
 * Main.go reports any error while preprocessing and exits 2 on its own.
 * What this file adds runs at load time (the filter's options and include
 * path) and after camlp5 has printed the output (the spelling check). If a
 * word is misspelled, the output file is removed and the program exits 1.
 *)
external exit : int -> unit = "caml_exit"

let check_spelling () =
   try
      Filter_exn.print_exn Dform.null_base None Term_grammar.raise_spelling_error ()
   with
      _ ->
         remove_output_file ();
         do_at_exit ();
         close_out stdout;
         close_out stderr;
         exit 1

let () =
   Arg.current := 1;
   Env_arg.parse spec add_anon_arg "MetaPRL compiler";
   set_include_path !include_path;
   let print_interf = !Pcaml.print_interf in
   let print_implem = !Pcaml.print_implem in
      Pcaml.print_interf := (fun x -> print_interf x; check_spelling ());
      Pcaml.print_implem := (fun x -> print_implem x; check_spelling ())

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
