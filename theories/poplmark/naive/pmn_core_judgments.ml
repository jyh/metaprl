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

reflected_logic Judgments =
struct
   (* Judgments *)
   declare typeclass Prop -> Term

   declare fsub_subtype{'ty1 : TyExp; 'ty2 : TyExp} : Prop
   declare fsub_member{'e : Exp; 'ty : TyExp} : Prop

   (* Manually code the well-formedness for sequents *)
   declare typeclass Judgment -> Perv!Judgment

   declare sequent [fsub] { Term : Term >- Term } : Term

   interactive fsub_sequent_is_judgment : <:xrule<
       meta_type{| <H> >- meta_member{C; "Prop"} |} -->
       meta_type{| <H> >- meta_member{"fsub"{| >- C |}; "Judgment"} |}
   >>
end

(*
 * -*-
 * Local Variables:
 * Fill-column: 120
 * End:
 * -*-
 * vim:ts=3:et:tw=120
 *)
