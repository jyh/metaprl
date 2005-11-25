(*
 * The D tactic performs a case selection on the conclusion opname.
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
 * Author: Jason Hickey <jyh@cs.cornell.edu>
 * Modified by: Aleksey Nogin <nogin@cs.cornell.edu>
 *)
extends Base_theory

open Basic_tactics

open Tactic_type

resource (term * (int -> tactic), int -> tactic) meta_elim
resource (term * intro_item, tactic) meta_intro

val process_meta_elim_resource_annotation :
   (Tactic.pre_tactic * elim_option list, term * (int -> tactic)) annotation_processor

val process_meta_intro_resource_annotation :
   (Tactic.pre_tactic * intro_option list, term * intro_item) annotation_processor

val wrap_intro : tactic -> intro_item
val intro_must_select : intro_item

(*
 * The inherited d tactic.
 *)
val d_prec : auto_prec

topval meta_dT : int -> tactic

(*
 * Run dT 0 so many times.
 *)
topval meta_dForT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
