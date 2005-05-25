doc <:doc<
   @begin[doc]
   @module[Itt_hoas_destterm]
   The @tt[Itt_hoas_destterm] module defines destructors for extracting
   from a bterm the components corresponding to the de Bruijn-like representation
   of that bterm.
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
extends Itt_hoas_operator
extends Itt_hoas_debruijn

declare is_var{'bt}
declare dest_bterm{'bt; l,r.'var_case['l; 'r]; op,subterms. 'op_case['op; 'subterms] }

