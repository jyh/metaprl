doc <:doc<
   Native sequent representation.  This representation of sequents
   is not a BTerm itself.  If you want to work in a theory where
   sequents are not part of your language, then you should probably
   use this representation, because it is easier to use.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2005 Mojave Group, Caltech

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Itt_hoas_sequent
extends Itt_hoas_sequent_term

doc docoff

doc <:doc<
   The << Member >> typeclass specifies the membership judgment.
>>
declare typeclass Member -> Dform

doc <:doc<
   The << meta_member{'e; 'ty} >> term specifies that the term << 'e >>
   has meta-type << 'ty >>.
>>
declare meta_member{'e : 'a; 'ty : 'b} : Member

doc docoff

(************************************************************************
 * Display forms.
 *)
dform meta_type_df : <:xterm< $`"meta_type" >> =
   `"meta_type"

dform meta_member_df : <:xterm< $`meta_member{e; ty} >> =
   szone pushm[3] slot{'e} `" " Mpsymbols!member `"M" hspace slot{'ty} popm ezone

dform meta_type_df2 : <:xterm< $'[d] "meta_type" >> =
   `"meta_type[" slot{'d} `"]"

dform meta_member_df2 : <:xterm< $'[d] meta_member{e; ty} >> =
   szone pushm[3] slot{'e} `" " Mpsymbols!member `"M[" slot{'d} `"]" hspace slot{'ty} popm ezone

dform bsequent_meta_type_df : bsequent{meta_type} =
   `"BM"

dform vsequent_meta_type_df : vsequent{meta_type} =
   `"VM"

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
