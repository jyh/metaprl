(*
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
doc <:doc<
   @parents
>>
extends Itt_sqsimple
extends Itt_image
extends Itt_tunion
extends Itt_nat
doc docoff

open Basic_tactics

(*
 * Special case where the index is nat, and the range is monotone.
 *)
interactive tunion_nat_sqsimple {| intro [] |} :
   [wf] sequent { <H>; i: nat >- 'B['i] Type } -->
   sequent { <H>; i: nat >- 'B['i] subtype 'B['i +@ 1] } -->
   sequent { <H>; i: nat >- sqsimple{'B['i]} } -->
   sequent { <H> >- sqsimple{Union i: nat. 'B['i]} }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
