(*
 * Define types over the state.
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

include Itt_theory
include Sil_types

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

prim_rw unfold_unit : Sil_types!unit <--> lambda{s. Itt_unit!unit}

prim_rw unfold_int : Sil_types!int <--> lambda{s. Itt_int!int}

prim_rw unfold_union : Sil_types!union{'A; 'B} <-->
   lambda{s. Itt_union!union{.'A 's; .'B 's}}

prim_rw unfold_prod : Sil_types!dprod{'A; v. 'B['v]} <-->
   lambda{s. Itt_dprod!prod{.'A 's; v. 'B['v] 's}}

prim_rw unfold_fun : Sil_types!"fun"{'A; v. 'B['v]} <-->
   lambda{s. Itt_rfun!"fun"{.'A 's; v. 'B['v] 's}}

prim_rw unfold_ref_type : Sil_types!ref_type <-->
   lambda{s. label_type}

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
