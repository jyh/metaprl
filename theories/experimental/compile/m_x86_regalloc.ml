(*
 * Perform a register allocation.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
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
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends Top_tacticals

open Lm_symbol
open Lm_printf

open M_standardize
open M_x86_backend
open M_x86_spill
open M_x86_coalesce
open M_ra_type
open M_ra_main

open Tactic_type.Tacticals
open Tactic_type.Sequent

module RegAlloc = MakeRegAlloc (Frame)

(*
 * Flatten the symbol table into a string table.
 *)
let rec flatten_var table v =
   try flatten_var table (SymbolTable.find table v) with
      Not_found ->
         v

let flatten_table table =
   SymbolTable.fold (fun stable v1 v2 ->
         SymbolTable.add stable v1 (flatten_var table v2)) SymbolTable.empty table

let table_colors table =
   SymbolTable.fold SymbolTable.add SymbolTable.empty table

let runT_aux contT p =
   let t = concl p in
   let blocks = Frame.blocks_of_term t in
      match RegAlloc.compile blocks with
         RegAllocSpill vars ->
            let _ =
               eprintf "*** Spills%t" eflush;
               SymbolSet.iter (fun s ->
                     eprintf "Spilling %s%t" (string_of_symbol s) eflush) vars
            in
               spillT vars thenT renameT thenT contT
       | RegAllocColor vars ->
            let vars = flatten_table vars in
            let svars = table_colors vars in
            let _ =
               eprintf "*** Colors%t" eflush;
               SymbolTable.iter (fun v1 v2 ->
                     eprintf "Coloring %s -> %s%t" (string_of_symbol v1) (string_of_symbol v2) eflush) svars
            in
               coalesceT vars thenT destandardize_debugT svars

let runT = argfunT runT_aux

let stepT =
   runT idT

let rec allocT_aux _ =
   runT (funT allocT_aux)

let allocT =
   funT allocT_aux

(*
 * Print the assembly to a file.
 *)
let printT_aux filename p =
   let out = Stdlib.open_out filename in
   let buf = formatter_of_out_channel out in
      pp_print_prog buf (concl p);
      close_out out;
      idT

let printT = argfunT printT_aux

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
