(*
 * Formalize a bit of artihmetic.
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
extends Base_theory

open Base_meta

open Tactic_type.Conversionals

declare number[i:n]
declare number{'i}

declare add{'i1; 'i2}
declare sub{'i1; 'i2}
declare mul{'i1; 'i2}
declare div{'i1; 'i2}

prim_rw reduce_add : add{number[i1:n]; number[i2:n]} <--> number{meta_sum[i1:n, i2:n]}
prim_rw reduce_sub : sub{number[i1:n]; number[i2:n]} <--> number{meta_diff[i1:n, i2:n]}
prim_rw reduce_mul : mul{number[i1:n]; number[i2:n]} <--> number{meta_prod[i1:n, i2:n]}
prim_rw reduce_div : div{number[i1:n]; number[i2:n]} <--> number{meta_quot[i1:n, i2:n]}
prim_rw reduce_number : number{meta_num[i:n]} <--> number[i:n]

let resource reduce +=
    [<< add{number[i1:n]; number[i2:n]} >>, (reduce_add thenC addrC[0] reduce_meta_sum  thenC reduce_number);
     << sub{number[i1:n]; number[i2:n]} >>, (reduce_sub thenC addrC[0] reduce_meta_diff thenC reduce_number);
     << mul{number[i1:n]; number[i2:n]} >>, (reduce_mul thenC addrC[0] reduce_meta_prod thenC reduce_number);
     << div{number[i1:n]; number[i2:n]} >>, (reduce_div thenC addrC[0] reduce_meta_quot thenC reduce_number)]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
