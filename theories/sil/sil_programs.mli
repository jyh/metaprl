(*
 * This is the definition of a Simple Imperative Language.
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

extends Base_theory

(*
 * Meta-terms.
 *)
declare "true"
declare "false"

(*
 * Numbers.
 *)
declare number[i:n]
declare "add"{'e1; 'e2}
declare "sub"{'e1; 'e2}
declare "if"{'e1; 'e2; 'e3; 'e4}

(*
 * Disjoint union.
 *)
declare inl{'e1}
declare inr{'e1}
declare decide{'e1; x. 'e2['x]; y. 'e3['y]}

(*
 * Tuples.
 *)
declare pair{'e1; 'e2}
declare spread{'e1; x, y. 'e2['x; 'y]}

(*
 * Reference cells.
 *)
declare pointer{'l}
declare ref{'e1}
declare deref{'e1}
declare assign{'e1; 'e2}
declare dot

(*
 * Functions.
 *)
declare lambda{v. 'e1['v]}
declare apply{'e1; 'e2}

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
