(*
 * The general theory for the M language.
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
extends M_cps
extends M_closure
extends M_prog
extends M_dead
extends M_inline

open M_cps
open M_closure
open M_prog
open M_dead
open M_inline

open Tactic_type.Tacticals
open Tactic_type.Conversionals

let compileT =
   (* CPS conversion *)
   cpsT

   (* Closure conversion *)
   thenT closeT

   (* Lift definitions to top level *)
   thenT progT

   (* Perform dead code elimination *)
   thenT deadT

   (* Perform inlining and constant folding *)
   thenT inlineT

   (* Another round of dead code elimination *)
   thenT deadT

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
