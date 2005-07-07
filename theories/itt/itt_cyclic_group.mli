(*
 * Cyclic groups.
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
 * Author: Xin Yu
 * Email : xiny@cs.caltech.edu
 *)

extends Itt_group
extends Itt_int_base
extends Itt_subset

open Tactic_type.Tactic

(************************************************************************
 * TERMS                                                               *
 ************************************************************************)

declare group_power{'g; 'a; 'n}
declare natpower{'g; 'a; 'n}
declare isCyclic{'g}
declare cycSubg{'g; 'a}

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval fold_group_power : conv
topval fold_natpower : conv
topval fold_isCyclic : conv
topval fold_cycSubg : conv

topval natpowerC : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
