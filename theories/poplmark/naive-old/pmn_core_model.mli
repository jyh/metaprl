(*
 * ITT model of core Fsub.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
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
extends Pmn_core_tast

open Basic_tactics

topval fold_ty_var_type : conv
topval fold_ty_exp : conv
topval fold_ty_top : conv
topval fold_ty_var : conv
topval fold_ty_fun : conv
topval fold_ty_all : conv

topval fold_var_type  : conv
topval fold_exp       : conv
topval fold_var       : conv
topval fold_apply     : conv
topval fold_lambda    : conv
topval fold_ty_apply  : conv
topval fold_ty_lambda : conv

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
