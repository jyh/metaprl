doc <:doc<
   @begin[doc]
   @module[Itt_synt_var]
   A deBruijn-like implementation of a type of bound variables.

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

   Authors: Aleksey Nogin <nogin@cs.caltech.edu>
            Alexei Kopylov <kopylov@cs.caltech.edu>
            Xin Yu <xiny@cs.caltech.edu>

   @end[license]
>>

extends Itt_nat


declare Var
declare var{'left; 'right}
declare left{'v}
declare right{'v}
declare depth{'v}
