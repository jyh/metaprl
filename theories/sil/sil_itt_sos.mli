(*
 * Operational semantics of the imperative programs,
 * coded in ITT.
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
 * Copyright (C) 1999 Jason Hickey, Cornell University
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

extends Itt_theory

extends Sil_state
extends Sil_programs
extends Sil_sos

open Basic_tactics

topval rwvalueT : term -> int -> tactic
topval rwvalueRevT : term -> int -> tactic
topval rwevalT : int -> tactic

topval squash_evalstoT : tactic
topval squash_valueT : tactic

topval fold_eq_int : conv
topval fold_neq_int : conv
topval fold_value : conv
topval fold_evalsto : conv
topval fold_eval : conv
topval fold_prog : conv
topval fold_match : conv
topval fold_val : conv
topval fold_progof : conv
topval fold_stateof : conv
topval fold_exprof : conv
topval fold_valueof : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
