(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Provides the primary interface to the MC compiler.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
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
 * Author: Brian Emre Aydemir
 * Email:  emre@its.caltech.edu
 *)

include Base_theory

open Symbol
open Fir

open Mp_mc_connect_exp

(*
 * Despite the apparently complexity, this is an identity operation for
 * an Fir.prog. We convert the function definitions (fundef SymbolTable.t)
 * to terms (term SymbolTable.t), and then back again.  Later, we'd
 * like to do optimizations and proofs after we converted to terms.
 *)

let compile prog =
   let term_table = SymbolTable.map term_of_fundef prog.prog_funs in
   (* Here, we'd do something like optimize or generate a proof. *)
   let new_prog_funs = SymbolTable.map fundef_of_term term_table in
      { prog with prog_funs = new_prog_funs }
