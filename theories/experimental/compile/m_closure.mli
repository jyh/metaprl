(*!
 * @begin[doc]
 * @module[M_closure]
 *
 * Closure conversion for the @emph{M} language.
 * @end[doc]
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

open Refiner.Refiner.TermType

open Tactic_type.Tacticals
open Tactic_type.Conversionals

(*
 * CPS resource
 *)
resource (term * conv, conv) closure

(*
 * The first three are for debugging.
 *)
topval frameT : tactic
topval abstractT : tactic
topval uncloseT : tactic
topval pushT : tactic

(*
 * This is the real closure conversion.
 *)
topval closeT : tactic

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
