(*
 * This module defines a notion of "squiggle-simple" type,
 * which are the type, where only squiggle-equal members 
 * are considered equal.
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
 * Copyright (C) 2004-2005 MetaPRL Group, Caltech
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
 * Modified by: Aleksey Nogin <nogin@cs.caltech.edu>
 *)
open Basic_tactics

resource (term * term list, term -> bool) sqsimple

val process_sqsimple_resource_annotation :
   ('a, term * term list) annotation_processor

declare sqsimple{'T}
declare sqsimple_type{'T}

topval fold_sqsimple : conv
topval fold_sqsimple_type : conv

val sqsimple_sq: term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)

