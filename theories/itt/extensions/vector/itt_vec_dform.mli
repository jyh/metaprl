(*
 * Generic utilities for core language.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2003-2004-2005 Mojave Group, Caltech
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
 * Author: Jason Hickey <jyh@cs.caltech.edu>
 * Modified By: Aleksey Nogin <nogin@cs.caltech.edu>
 *)
extends Base_theory

(*
 * Sequent display forms.
 *)
declare display_sequent{'s : Dform} : Dform
declare display_hyp{'ext : ty_sequent{ty_hyp{'ty_var; 'ty_hyp}; 'ty_concl; 'ty_seq}; v. 'e['v] : Dform} : Dform
declare display_hyp_sep{'ext : ty_sequent{ty_hyp{'ty_var; 'ty_hyp}; 'ty_concl; 'ty_seq}} : Dform
declare display_concl{'ext : ty_sequent{ty_hyp{'ty_var; 'ty_hyp}; 'ty_concl; 'ty_seq}; 'e : Dform} : Dform

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
