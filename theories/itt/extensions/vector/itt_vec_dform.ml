(*
 * Generic utilities for the @emph{core} language.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003-2004,-2005 Mojave Group, Caltech
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
 * Author: Jason Hickey @email{jyh@cs.caltech.edu}
 * Modified By: Aleksey Nogin @email{nogin@cs.caltech.edu}
 * @end[license]
 *)
extends Top_tacticals
extends Base_theory

open Basic_tactics

open Simple_print.SimplePrint

(************************************************************************
 * Terms
 *)

(* Private terms *)
declare display_hyps{'s : Dform} : Dform

(* Wrap the sequent argument to prevent recursive display *)
declare wrap_arg{'ext : ty_sequent{ty_hyp{'ty_var; 'ty_hyp}; 'ty_concl; 'ty_seq}} : ty_sequent{ty_hyp{'ty_var; 'ty_hyp}; 'ty_concl; 'ty_seq}

(************************************************************************
 * Display forms
 *)
dform display_sequent_df : display_sequent{sequent ['ext] { <H> >- 'e }} =
   display_hyps{sequent [wrap_arg{'ext}] { <H> >- 'e }}

dform display_hyps_nil_df : display_hyps{sequent [wrap_arg{'ext}] { >- 'e }} =
   display_concl{'ext; 'e}

dform display_hyps_cons_df : display_hyps{sequent [wrap_arg{'ext}] { x: 't; <H> >- 'e }} =
   display_hyp{'ext; x. 't}
   display_hyp_sep{'ext}
   display_hyps{sequent [wrap_arg{'ext}] { <H> >- 'e }}

dform display_hyps_cons_df2 : display_hyps{sequent [wrap_arg{'ext}] { x: 't >- 'e }} =
   display_hyp{'ext; x. 't}
   display_hyps{sequent [wrap_arg{'ext}] { >- 'e }}

dform display_hyp_sep_df : display_hyp_sep{'ext} =
   `"," hspace

(*
 * Strip sequent_args if necessary.
 * Note, you can always override this by defining a more specific display form.
 *)
dform context_hyp_df : display_hyp{'ext; x. df_context{'c}} =
   df_context{'c}

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
