(*
 * Remove moves that are to the same register.
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
extends M_standardize
extends M_x86_backend

open Lm_symbol
open Lm_format
open Lm_symbol_format

open M_standardize
open M_x86_inst_type
open M_x86_term
open M_x86_backend

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

(*
 * Coalesce let-moves.
 *)
prim_rw reduce_let :
   Mov{Register{'v1}; v2. 'e['v2]} <--> 'e['v1]

(*
 * Two vars are equal.
 *)
let table_lookup table v =
   try SymbolTable.find table v with
      Not_found ->
         v

let table_equal table v1 v2 =
   Lm_symbol.eq (table_lookup table v1) (table_lookup table v2)

(*
 * Coalesce moves.
 *)
let coalesceC table =
   (* Have the rewriter search for the occurrence *)
   let convC e =
      let t = env_term e in
         match dest_inst_term t with
            Mov (Register src, dst, _)
            when table_equal table src dst ->
               if false then
                  eprintf "Coalescing %a = %a@." pp_print_symbol src pp_print_symbol dst;
               reduce_let
          | _ ->
               failC
   in
      funC convC

(*
 * Split a spill.
 *)
let coalesceT table =
   rw (repeatC (higherC (coalesceC table))) 0

(*
 * Initial variable renaming.
 *)
let renameT_aux p =
   let table = rename_term (concl p) in
   let table = SymbolTable.fold SymbolTable.add SymbolTable.empty table in
      destandardizeT table

let renameT =
   standardizeT
   thenT funT renameT_aux

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
