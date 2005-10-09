(*
 * Reduction.
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
extends Pmn_core_model

open Basic_tactics

(*
 * Functions and variables are values.
 *)
interactive value_wf {| intro [] |} : <:itt_rule<
    <H> >- e IN Exp -->
    <H> >- (value e) type
>>

interactive value_var {| intro [] |} : <:itt_rule<
    <H> >- value exp { ~v }
>>

interactive value_fun {| intro [] |} : <:itt_rule<
    <H> >- value exp { fun x : t -> e[x] }
>>

interactive value_Fun {| intro [] |} : <:itt_rule<
    <H> >- value exp { Fun X <: t -> e[X] }
>>

interactive not_value_apply : <:itt_rule<
    <H> >- e1 IN Exp -->
    <H> >- e2 IN Exp -->
    <H> >- not (value exp { e1 e2 })
>>

interactive not_value_ty_apply : <:itt_rule<
    <H> >- e IN Exp -->
    <H> >- ty IN TyExp -->
    <H> >- not (value exp { e{ty} })
>>

(*
 * Call-by-value reduction.
 *)
interactive reduce_wf {| intro [] |} : <:itt_rule<
    <H> >- e1 IN Exp -->
    <H> >- e2 IN Exp -->
    <H> >- (e1 ==> e2) type
>>

interactive reduce_value {| elim [] |} 'H : <:itt_rule<
    <H> >- e1 IN Exp -->
    <H> >- value e1 -->
    <H>; e1 ==> e2; <J> >- C
>>

interactive reduce_beta {| intro [] |} : <:itt_rule<
    <H> >- exp { (fun x: t -> e1[x]) e2 } ==> e1[e2]
>>

interactive reduce_type_beta {| intro [] |} : <:itt_rule<
    <H> >- exp { (Fun X <: t1 -> e[X]){t2} } ==> e[t2]
>>

interactive reduce_apply1 : <:itt_rule<
    <H> >- e1 ==> e2 -->
    <H> >- exp { e1 e3 } ==> exp { e2 e3 }
>>

interactive reduce_apply2 : <:itt_rule<
    <H> >- value v -->
    <H> >- e1 ==> e2 -->
    <H> >- exp { v e1 } ==> exp { v e2 }
>>

interactive reduce_apply_fun {| intro [] |} : <:itt_rule<
    <H> >- e1 ==> e2 -->
    <H> >- exp { e1{t} } ==> exp { e2{t} }
>>

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
