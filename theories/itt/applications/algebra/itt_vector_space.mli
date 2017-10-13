(*
 * Vector spaces.
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
 * Copyright (C) 1997-2017 MetaPRL Group
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
 * Email : jasonh@gmail.com
 *)

extends Itt_field2
extends Itt_labels

open Tactic_type.Tactic

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare "vec" : RecordLabel
declare "0v" : RecordLabel
declare "+|" : RecordLabel
declare "*|" : RecordLabel

declare pre_vector_space[i:l]

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval unfold_pre_vector_space : conv
topval unfold_vs_add_is_commutative : conv
topval unfold_vs_add_is_assoc : conv
topval unfold_vs_zero_is_identity : conv
topval unfold_vs_add_has_inverse : conv
topval unfold_vs_mul_is_compat : conv
topval unfold_vs_mul_has_identity : conv
topval unfold_vs_mul_vec_distrib : conv
topval unfold_vs_mul_scalar_distrib : conv
topval unfold_is_vector_space : conv

topval fold_pre_vector_space : conv
topval fold_is_vector_space : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
