(*
 * Include the HOAS base theory.
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
extends Reflect_itt_hoas_base_theory

open Basic_tactics

(*
 * The logic.
 *)
define unfold_base_theory : base_theory <--> <:xterm<
   "itt_hoas_base_theory"
>>

interactive base_theory_wf {| intro |} : <:xrule<
   <H> >- "base_theory" in Logic
>>

interactive elim_start_base_theory {| elim |} 'H : <:xrule<
   <H>; x: SimpleStep{premises; goal; witness; "itt_hoas_base_theory"}; <J[x]> >- C[x] -->
   <H>; x: SimpleStep{premises; goal; witness; "base_theory"}; <J[x]> >- C[x]
>>

interactive elim_base_theory {| elim |} 'H : <:xrule<
   <H>; x: ProvableSequent{"itt_hoas_base_theory"; e}; <J[x]> >- C[x] -->
   <H>; x: ProvableSequent{"base_theory"; e}; <J[x]> >- C[x]
>>

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
