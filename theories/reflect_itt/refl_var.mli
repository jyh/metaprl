(*
 * Variables are a list of atoms and ints.
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

include Itt_theory

open Tactic_type.Conversionals
open Tactic_type.Tacticals

declare vnil
declare var[t:t]
declare ivar{'i; 'v}
declare tvar{'t; 'v}
declare var_type
declare eq_varc{'v1; 'v2}
declare eq_var{'v1; 'v2}

topval unfold_vnil : conv
topval unfold_var : conv
topval unfold_ivar : conv
topval unfold_tvar : conv
topval unfold_var_type : conv
topval unfold_eq_varc : conv
topval unfold_eq_var : conv

topval fold_vnil : conv
topval fold_var : conv
topval fold_ivar : conv
topval fold_tvar : conv
topval fold_var_type : conv
topval fold_eq_varc : conv
topval fold_eq_var : conv

topval varSqequalT : tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
