(*
 * Klein 4-group.
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
extends Czf_itt_singleton
extends Czf_itt_union

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare klein4          (* The label representing the klein 4-group *)
declare k0              (* Identity of the group *)
declare k1              (* Element of the group *)
declare k2              (* Element of the group *)
declare k3              (* Element of the group *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * The group table is
 *
 *          | k0 k1 k2 k3
 *       ---|-------------
 *        k0| k0 k1 k2 k3
 *        k1| k1 k0 k3 k2
 *        k2| k2 k3 k0 k1
 *        k3| k3 k2 k1 k0
 *
 *)
rewrite unfold_klein4_car : car{klein4} <-->
   union{sing{k0}; union{sing{k1}; union{sing{k2}; sing{k3}}}} 
rewrite unfold_klein4_op00 : op{klein4; k0; k0} <--> k0
rewrite unfold_klein4_op01 : op{klein4; k0; k1} <--> k1
rewrite unfold_klein4_op02 : op{klein4; k0; k2} <--> k2
rewrite unfold_klein4_op03 : op{klein4; k0; k3} <--> k3
rewrite unfold_klein4_op10 : op{klein4; k1; k0} <--> k1
rewrite unfold_klein4_op11 : op{klein4; k1; k1} <--> k0
rewrite unfold_klein4_op12 : op{klein4; k1; k2} <--> k3
rewrite unfold_klein4_op13 : op{klein4; k1; k3} <--> k2
rewrite unfold_klein4_op20 : op{klein4; k2; k0} <--> k2
rewrite unfold_klein4_op21 : op{klein4; k2; k1} <--> k3
rewrite unfold_klein4_op22 : op{klein4; k2; k2} <--> k0
rewrite unfold_klein4_op23 : op{klein4; k2; k3} <--> k1
rewrite unfold_klein4_op30 : op{klein4; k3; k0} <--> k3
rewrite unfold_klein4_op31 : op{klein4; k3; k1} <--> k2
rewrite unfold_klein4_op32 : op{klein4; k3; k2} <--> k1
rewrite unfold_klein4_op33 : op{klein4; k3; k3} <--> k0
rewrite unfold_klein4_id   : id{klein4} <--> k0
rewrite unfold_klein4_inv0 : inv{klein4; k0} <--> k0
rewrite unfold_klein4_inv1 : inv{klein4; k1} <--> k1
rewrite unfold_klein4_inv2 : inv{klein4; k2} <--> k2
rewrite unfold_klein4_inv3 : inv{klein4; k3} <--> k3

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
