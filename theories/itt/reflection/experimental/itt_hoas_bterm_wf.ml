doc <:doc<
   @module[Itt_hoas_bterm_wf]
   The @tt[Itt_hoas_bterm_wf] module defines additional well-formedness
   rules for BTerms.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2005, MetaPRL Group

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}

   @end[license]
   @parents
>>
extends Itt_hoas_bterm
extends Itt_hoas_util

doc docoff

open Basic_tactics

doc <:doc<
   Reductions on bterms.
>>
define unfold_bflatten : bflatten{'l} <-->
   it

interactive_rw reduce_bind_mk_bterm {| reduce |} :
   bind{x. mk_bterm{'n; 'op; 'subterms['x]}}
   <-->
   mk_bterm{'n +@ 1; 'op; bflatten{bind{x. 'subterms['x]}}}

doc <:doc<
   Well-formedness of vector binders.
>>
interactive bterm_vec_wf {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'd in nat } -->
   sequent { <H> >- bind{'n; v. mk_term{'op; 'subterms['v]}} in BTerm{'d} }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
