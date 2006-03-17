(*
 * Judgments in fsub.
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
extends Pmn_core_terms

open Basic_tactics
open Itt_equal
open Itt_dfun

(************************************************************************
 * Display.
 *)
dform ty_power_df : <:xterm< TyPower{ty} >> =
   `"<: " slot{'ty}

dform fsub_df : <:xterm< "fsub" >> =
   `"fsub"

dform fsub_subtype_df : parens :: "prec"[prec_equal] :: <:xterm< fsub_subtype{t1; t2} >> =
   szone pushm[3] slot{'t1} `" <:" hspace slot{'t2} popm ezone

dform fsub_member_df : parens :: "prec"[prec_apply] :: <:xterm< fsub_member{e; ty} >> =
   szone pushm[3] slot{'e} `" " Mpsymbols!member hspace slot{'ty} popm ezone

dform fsub_Prop_df : <:xterm< "Prop" >> =
   `"Prop"

dform fsub_Judgment_df : <:xterm< "Judgment" >> =
   `"Judgment"

(*
 * -*-
 * Local Variables:
 * Fill-column: 120
 * End:
 * -*-
 * vim:ts=3:et:tw=120
 *)
