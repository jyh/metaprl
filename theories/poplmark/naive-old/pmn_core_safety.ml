(*
 * Preservation and progress.
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
extends Pmn_core_type
extends Pmn_core_sos
extends Pmn_core_model
extends Pmn_core_final

open Basic_tactics

interactive preservation 'e1 : <:itt_rule<
    <H> >- t IN TyExp -->
    <H> >- e1 IN Exp -->
    <H> >- e2 IN Exp -->
    <H> >- e1 :: t -->
    <H> >- e1 ==> e2 -->
    <H> >- e2 :: t
>>

interactive progress 't : <:itt_rule<
    <H> >- t IN TyExp -->
    <H> >- e1 IN Exp -->
    <H> >- e1 :: t -->
    <H> >- value e1 || exists e2: Exp. (e1 ==> e2)
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
