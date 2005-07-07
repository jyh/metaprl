(*
 * Equality on sets.
 * We make this dependent on membership, rather than the opposite.
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

extends Czf_member;;
extends Czf_all;;
extends Czf_implies;;
extends Czf_and;;

declare equal{'A; 'B};;

(*
 * Extensionality.
 * Perhaps there is a better way to formulate this.
 *)
rule extensional_equal :
   sequent { <H> >- "all"{x. "all"{y. equal{'x; 'y} => "all"{z. member{'z; 'x} => member{'z; 'y}}}} };;

(*
 * Membership is functional.
 *)
rule mem_fun :
   sequent { <H> >- "all"{x. "all"{y. "all"{z. (equal{'x; 'y} /\ member{'x; 'z}) => member{'y; 'z}}}} };;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
