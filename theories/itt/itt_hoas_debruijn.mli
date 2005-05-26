doc <:doc<
   @begin[doc]
   The @tt[Itt_hoas_debruij] module defines a mapping from de Bruijn-like
   representation of syntax into the HOAS.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

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

   Author: Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>

extends Itt_hoas_base
extends Itt_hoas_vector
extends Itt_nat
extends Itt_list2

declare var{'left; 'right}
declare mk_bterm{'n; 'op; 'btl}
declare bdepth{'bt}
declare left{'v}
declare right{'v}
declare get_op{'bt; 'op}
declare subterms{'bt}
declare not_found
define iform unfold_get_op1:
   get_op{'bt} <--> get_op{'bt; not_found}
