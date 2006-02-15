(*
 * Typed core language.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003-2006 Mojave Group, Caltech
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
extends Base_theory
extends Itt_hoas_theory

open Basic_tactics

(************************************************************************
 * Types.
 *)
declare typeclass TyExp -> Term

declare TyTop : TyExp
declare TyFun{'ty_domain : TyExp; 'ty_range : TyExp} : TyExp
declare TyAll{'ty_bound : TyExp; x : TyExp. 'ty['x] : TyExp} : TyExp

(************************************************************************
 * Expressions.
 *)
declare typeclass Exp -> Term

(*
 * Normal abstraction and application.
 *)
declare Lambda{'ty_arg : TyExp; x : Exp. 'e['x] : Exp} : Exp
declare Apply{'e1 : Exp; 'e2 : Exp} : Exp

(*
 * Type abstraction and application.
 *)
declare TyLambda{'ty_bound : TyExp; x : TyExp. 'e['x] : Exp} : Exp
declare TyApply{'e : Exp; 'ty_arg : TyExp} : Exp

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
