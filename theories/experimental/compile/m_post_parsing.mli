(*
 * Post-parsing transformations.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Adam Granicz, Caltech
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
 * Author: Adam Granicz
 * @email{granicz@cs.caltech.edu}
 * @end[license]
 *)
extends M_ir

open Refiner.Refiner.Term
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Tacticals
open Tactic_type.Conversionals

(*
 * PP transformer.
 *)
declare PP{'e}

(*
 * PP resource
 *)
resource (term * conv, conv) pp

(*
 * For debugging.
 *)
topval ppTopC : conv
topval ppC : conv

topval ppT : tactic

