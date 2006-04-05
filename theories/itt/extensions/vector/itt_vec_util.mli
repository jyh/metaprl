(*
 * Some frequently-used utilities.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2006 Mojave Group, Caltech
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
open Basic_tactics

(*
 * In many case, we have rules that say the the hyp values do not matter.
 * The rules have the following form:
 *
 * rewrite foo Perv!bind{x. arg{| <J[x]> >- e |}} :
 *    arg{| <J[t]> >- e |}
 *    <-->
 *    arg{| <J[it]> >- e |}
 *
 * The following function takes a rule of this form and computes
 * and appropriate argument.
 *)
val squash_rewrite_arg : term -> term

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
