(*
 * Dependent vector lists.
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
extends Itt_vec_list1

(*
 * Dependent vector list.
 *)
declare sequent [vdlist{'f}] { Term : Term >- Term } : Term

doc <:doc<
   The term <:xterm< vlistwf{A; B; C}{| <J> >- D |} >> specifies that
   if all the hyp bindings have type << 'A >>, then the hyp values
   have type << 'B >>, and the conclusion has type << 'C >>.
>>
declare sequent [vlistwf{'A; 'B; 'C}] { Term : Term >- Term } : Term

(*
 * The vlistlistwf form is defined as <:xterm< vlistwf{top; list; top}{| <J> >- C |} >>
 *)
declare sequent [vlistlistwf] { Term : Term >- Term } : Term

(*
 * -*-
 * Local Variables:
 * Fill-column: 120
 * End:
 * -*-
 * vim:ts=3:et:tw=120
 *)
