(*
 * Subset collection.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2000 Jason Hickey, Caltech
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
 * jyh@cs.caltech.edu
 *)

extends Czf_itt_subset
extends Czf_itt_rel

open Refiner.Refiner.TermType
open Tactic_type.Tacticals

declare power{'s1; 's2}

rewrite unfold_scoll : power{'s1; 's2} <-->
   set_ind{'s1; T1, f1, g1.
      set_ind{'s2; T2, f2, g2.
         collect{.'T1 -> 'T2; x. collect{'T1; y. 'f2 ('x 'y)}}}}

rewrite reduce_scoll : power{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
    collect{.'T1 -> 'T2; x. collect{'T1; y. 'f2['x 'y]}}

topval powerT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
