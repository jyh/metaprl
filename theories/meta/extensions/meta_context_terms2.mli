(*
 * Context rewrites.
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
extends Meta_rewrite
extends Meta_context_ind1

(*
 * In the common case, the sequents are defined over terms.
 *)
declare sequent [TermSequent] { Term : Term >- Term } : SequentCore{Term; Term; Term}

(*
 * Split the hyp.
 *)
declare sequent_ind{u : 'b, v : HFun{'a; 'b; 'c}. 'step['u; 'v] : 'c; 'e : SequentCore{'a; 'b; 'c}} : 'c

declare sequent_ind{x : 'c. 'concl['x] : 'result;
                    u : 'b, v : HFun{'a; 'b; 'result}. 'step['u; 'v] : 'result;
                    'e : SequentCore{'a; 'b; 'c}} : 'result

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
