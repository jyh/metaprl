(*
 * A squashed form of induction.
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
extends Meta_context_terms

declare squash_sequent_ind{h: HFun{Term; 'b; 'result}. 'step['h] : 'result; 'e : Sequent{Term; 'b; 'result}} : 'result
declare squash_sequent_ind{u : 'b, v : HFun{Term; 'b; 'c}. 'step['u; 'v] : 'c; 'e : Sequent{Term; 'b; 'c}} : 'c

(*
 * -*-
 * Local Variables:
 * Fill-column: 120
 * End:
 * -*-
 * vim:ts=3:et:tw=120
 *)
