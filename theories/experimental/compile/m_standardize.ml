(*
 * Rename all binding variables so that they
 * are all different.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
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
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends M_ir

open Refiner.Refiner.TermSubst

open Tactic_type.Sequent

open Top_tacticals

(*
 * Alpha equality.
 *)
declare equal{'e1; 'e2}

interactive alpha_equal :
   sequent [m] { 'H >- equal{'e; 'e} }

interactive subst 'e2 :
   sequent [m] { 'H >- 'e2 } -->
   ["wf"] sequent [m] { 'H >- equal{'e1; 'e2} } -->
   sequent [m] { 'H >- 'e1 }

let standardizeT =
   (fun p -> subst (standardize (concl p)) p)
   thenWT alpha_equal

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
