(*
 * Group Builder.
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
 * Copyright (C) 2002 Xin Yu, Caltech
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
 * Author: Xin Yu
 * Email : xiny@cs.caltech.edu
 *)

extends Czf_itt_group
extends Czf_itt_subset

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(* Build a group h from group g. The underlying set of h is s;
 * the operation in h is the same as in g. s must be a subset of
 * the underlying set of g.
 *)
declare group_bvd{'h; 'g; 's}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

rewrite unfold_group_bvd : group_bvd{'h; 'g; 's} <-->
   (group{'h} & group{'g} & isset{'s} & \subset{'s; car{'g}} & equal{car{'h}; 's} & (all a: set. all b: set. (mem{'a; car{'h}} => mem{'b; car{'h}} => eq{op{'h; 'a; 'b}; op{'g; 'a; 'b}})))

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
