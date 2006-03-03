doc <:doc<
   @module[Itt_hoas_eta]

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2006 MetaPRL Group, California Institute of Technology

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

   Authors:
      Xin Yu @email{xiny@cs.caltech.edu}

   @end[license]
   @parents
>>
extends Itt_hoas_bterm
doc docoff

open Basic_tactics

doc terms

define unfold_eta: eta{'n; 'e} <--> bind{'n; x. substl{'e; 'x}}
define unfold_etal: etal{'n; 'tl} <--> map{x. eta{'n; 'x}; 'tl}

doc rules

interactive_rw eta_nil {| reduce |} :
   etal{'n; nil} <--> nil

interactive_rw eta_cons {| reduce |} :
   etal{'n; cons{'h; 't}} <--> eta{'n; cons{'h; etal{'n; 't}}}

interactive_rw mk_bterm_eta :
   'btl in list -->
   'n in nat -->
   'm in nat -->
   'm <= 'n -->
   mk_bterm{'n; 'op; etal{'m; 'btl}} <--> mk_bterm{'n; 'op; 'btl}

interactive_rw mk_bterm_eta1 {| reduce |} :
   'btl in list -->
   'n in nat -->
   mk_bterm{'n; 'op; etal{'n; 'btl}} <--> mk_bterm{'n; 'op; 'btl}

interactive_rw mk_bterm_eta_expand :
   'btl in list -->
   'n in nat -->
   mk_bterm{'n; 'op; 'btl} <--> mk_bterm{'n; 'op; etal{'n; 'btl}}

interactive_rw eta_mk_bterm {| reduce |} :
   'n in nat -->
   'm in nat -->
   'm <= 'n -->
   eta{'m; mk_bterm{'n; 'op; 'btl}} <--> mk_bterm{'n; 'op; 'btl}

interactive mk_bterm_wf {| intro [] |} :
   [wf] sequent{ <H> >- 'depth in nat } -->
   [wf] sequent{ <H> >- 'op in Operator } -->
   [wf] sequent{ <H> >- etal{'depth; 'subterms} in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'depth; shape{'op}; etal{'depth; 'subterms}} } -->
   sequent{ <H> >- mk_bterm{'depth; 'op; 'subterms} in BTerm }

interactive mk_bterm_wf2 {| intro [] |} :
   [wf] sequent{ <H> >- 'd1 = 'd2 in nat } -->
   [wf] sequent{ <H> >- 'op in Operator } -->
   [wf] sequent{ <H> >- etal{'d1; 'subterms} in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'d1; shape{'op}; etal{'d1; 'subterms}} } -->
   sequent{ <H> >- mk_bterm{'d1; 'op; 'subterms} in BTerm{'d2} }

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
