(*
 * Define well-typedness as a proposition.
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

open Lm_printf
open Simple_print

(*
let x = <:itt<
    fix mem venv e ty ->
       match e with
          (* Var *) v ->
             venv v = ty in TyExp
        | (* Apply *) e1, e2 ->
             exists s: TyExp.
                 (mem venv e1 (type { s -> ty }) && mem venv e2 s)
        | (* Lambda *) s, f ->
             exists ty2: TyExp.
                   (ty = type { s -> ty2 } in TyExp)
                && (all x: Var. (venv x = s in TyExp) => mem venv (f x) ty2)
       end
>>

let s = SimplePrint.string_of_term x in
   eprintf "%s@." s
   *)

(*
 * Propositional definition.
 *)
define unfold_mem : mem <--> <:itt<
    fix mem venv e ty ->
       match e with
          (* Var *) v ->
             venv v = ty in TyExp
        | (* Apply *) e1, e2 ->
             exists s: TyExp.
                 (mem venv e1 (type { s -> ty }) && mem venv e2 s)
        | (* Lambda *) s, f ->
             exists ty2: TyExp.
                   (ty = type { s -> ty2 } in TyExp)
                && (all x: Var. (venv x = s in TyExp) => mem venv (f x) ty2)
       end
>>

prim_rw unfold_member :
    member{'e; 'ty}
    <-->
    all venv : Var -> TyExp. mem 'venv 'e 'ty

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
