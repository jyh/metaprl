(*
 * Create an ediable rewrite object.
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

extends Shell_sig
extends Package_info
extends Summary

open Refiner.Refiner.RefineError
open Dform

open Summary
open Shell_sig
open Package_info

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * A window is either a text window or an HTML window.
 *)
type java_window =
   { pw_port : Java_mux_channel.session;
     pw_base : dform_mode_base;
     pw_menu : Java_display_term.t
   }

type text_window =
   { df_base : dform_mode_base;
     df_mode : string;
     mutable df_width : int
   }

type window =
   JavaWindow of java_window
 | TextWindow of text_window
 | TexWindow of text_window
 | BrowserWindow of text_window

(************************************************************************
 * WINDOWS                                                              *
 ************************************************************************)

(*
 * Create a window from the description.
 *)
let create_window = function
   DisplayText (base, mode) ->
      TextWindow { df_base = base; df_mode = mode; df_width = 80 }
 | DisplayTex base ->
      TexWindow { df_base = base; df_mode = "tex"; df_width = 80 }
 | DisplayBrowser base ->
      BrowserWindow { df_base = base; df_mode = "html"; df_width = 80 }
 | DisplayJava (port, base) ->
      let menu = Java_display_term.create_term port base in
         JavaWindow { pw_port = port; pw_base = base; pw_menu = menu }

(*
 * Update the width based on the terminal.
 *)
let update_terminal_width window =
   match window with
      TextWindow info ->
         info.df_width <- Mp_term.term_width Pervasives.stdout info.df_width;
         window
    | TexWindow _
    | JavaWindow _
    | BrowserWindow _ ->
         window

(*
 * Copy the window.
 *)
let new_window = function
   JavaWindow { pw_port = port; pw_base = base } ->
      JavaWindow { pw_port = port; pw_base = base; pw_menu = Java_display_term.create_term port base }
 | TextWindow _
 | TexWindow _
 | BrowserWindow _ as window ->
      window

(*
 * Display a term in the window.
 *)
let display_term window term =
   match update_terminal_width window with
      TextWindow { df_base = base; df_mode = mode; df_width = width } ->
         let df = get_mode_base base mode in
         let buf = Lm_rformat.new_buffer () in
            Dform.format_term df buf term;
            Lm_rformat_text.print_text_channel width buf stdout;
            flush stdout
    | TexWindow { df_base = base; df_mode = mode; df_width = width } ->
         let df = get_mode_base base mode in
         let buf = Lm_rformat.new_buffer () in
            Dform.format_term df buf term;
            Lm_rformat_tex.print_tex_channel width buf stdout;
            flush stdout
    | JavaWindow { pw_menu = menu } ->
         Java_display_term.set_dir menu "/";
         Java_display_term.set menu term
    | BrowserWindow { df_base = base; df_mode = mode } ->
         let df = get_mode_base base mode in
         let buf = Lm_rformat.new_buffer () in
            Dform.format_term df buf term;
            Browser_display_term.set_main buf

(************************************************************************
 * SHELL INTERFACE                                                      *
 ************************************************************************)

(*
 * Error handler.
 *)
let raise_edit_error s =
   raise (RefineError ("Shell_root", StringError s))

(*
 * Build the shell interface.
 *)
let rec edit pack window =
   let edit_display _ =
      (* Display the roots of the package *)
      let packs = Package.packages pack in
      let term = mk_packages_term (List.map (fun root -> mk_package_term (Package.name root)) packs) in
         display_term window term
   in
   let edit_copy () =
      edit pack (new_window window)
   in
   let not_a_rule _ =
      raise_edit_error "this is not a rule or rewrite"
   in
   let edit_save () =
      raise_edit_error "list of packages can't be saved"
   in
   let edit_check _ =
      raise_edit_error "check the complete set of packages? Use check_all."
   in
   let edit_root () =
      ()
   in
   let edit_up i =
      ()
   in
   let edit_down i =
      ()
   in
   let edit_undo () =
      ()
   in
   let edit_redo () =
      ()
   in
   let edit_addr addr =
      ()
   in
   let edit_info () =
      raise_edit_error "no info for the root packages"
   in
   let edit_refine _ _ _ =
      raise_edit_error "can't refine the root packages"
   in
   let edit_interpret command =
      raise_edit_error "this is not a proof"
   in
   let edit_get_contents () =
      raise_edit_error "can only retrieve contents of an individual item, not of a root package"
   in
      { edit_display = edit_display;
        edit_get_contents = edit_get_contents;
        edit_get_terms = not_a_rule;
        edit_copy = edit_copy;
        edit_set_goal = not_a_rule;
        edit_set_redex = not_a_rule;
        edit_set_contractum = not_a_rule;
        edit_set_assumptions = not_a_rule;
        edit_set_params = not_a_rule;
        edit_get_extract = not_a_rule;
        edit_save = edit_save;
        edit_check = edit_check;
        edit_root = edit_root;
        edit_up = edit_up;
        edit_down = edit_down;
        edit_addr = edit_addr;
        edit_info = edit_info;
        edit_refine = edit_refine;
        edit_undo = edit_undo;
        edit_redo = edit_redo;
        edit_interpret = edit_interpret
      }

let create pack window =
   let window = create_window window in
      edit pack window

let view pack window =
   edit pack (create_window window)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
