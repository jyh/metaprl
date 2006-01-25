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

reflected_logic Judgments =
struct
   (* Judgments *)
   declare typeclass Prop -> Term

   declare fsub_subtype{'ty1 : TyExp; 'ty2 : TyExp} : Prop
   declare fsub_member{'e : Exp; 'ty : TyExp} : Prop

   (* Manually code the well-formedness for sequents *)
   declare typeclass Judgment -> Perv!Judgment
   declare typeclass Hyp -> Term

   declare TyVal{'ty : TyExp} : Hyp
   declare TyPower{'ty : TyExp} : Hyp

   (*
    * Sequents have dependent types.
    * For now, we'll define the type judgments manually,
    * rather than using existential types.
    *)
   declare sequent [fsub] { Term : Hyp >- Prop } : Judgment

   interactive fsub_sequent_is_judgment_concl : <:xrule<
       meta_type{| <H> >- meta_member{C; "Prop"} |} -->
       meta_type{| <H> >- meta_member{fsub{| >- C |}; "Judgment"} |}
   >>

(*
   interactive fsub_sequent_is_judgment_val : <:xrule<
       meta_type{| <H> >- meta_member{ty; "TyExp"} |} -->
       meta_type{| <H>; x: "Exp" >- meta_member{fsub{| <J[x]> >- C[x] |}; "Judgment"} |} -->
       meta_type{| <H> >- meta_member{fsub{| x: TyVal{ty}; <J[x]> >- C[x] |}; "Judgment"} |}
   >>
 *)
end

(************************************************************************
 * Display.
 *)
declare df_depth{'d : Dform} : Dform

dform df_depth_df_any : df_depth{'d} =
   `"[" 'd `"]"

dform df_depth_df_zero : df_depth{0} =
   `""

dform ty_power_df : <:xterm< $'[d] TyPower{ty} >> =
   `"<:" df_depth{'d} `" " slot{'ty}

dform ty_val_df : <:xterm< $'[d] TyVal{ty} >> =
   `":" df_depth{'d} `" " slot{'ty}

dform fsub_df : <:xterm< $'[d] "fsub" >> =
   `"fsub" df_depth{'d}

dform fsub_subtype_df : parens :: "prec"[prec_equal] :: <:xterm< $'[d] fsub_subtype{t1; t2} >> =
   szone pushm[3] slot{'t1} `" <:" df_depth{'d} hspace slot{'t2} popm ezone

dform fsub_member_df : parens :: "prec"[prec_apply] :: <:xterm< $'[d] fsub_member{e; ty} >> =
   szone pushm[3] slot{'e} `" " Mpsymbols!member df_depth{'d} hspace slot{'ty} popm ezone

dform fsub_Prop_df : <:xterm< $'[d] "Prop" >> =
   `"Prop" df_depth{'d}

dform fsub_Judgment_df : <:xterm< $'[d] "Judgment" >> =
   `"Judgment" df_depth{'d}

(*
 * -*-
 * Local Variables:
 * Fill-column: 120
 * End:
 * -*-
 * vim:ts=3:et:tw=120
 *)
