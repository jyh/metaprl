doc <:doc< 
   @begin[doc]
   @module[Itt_antiquotient]
  
   See @cite[Nog02c], Section 6 for explanations.
  
   ----------------------------------------------------------------
  
   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.
  
   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.
  
   Copyright (C) 1998 Jason Hickey, Cornell University
  
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
  
   Author: Aleksey Nogin @email{nogin@cs.cornell.edu}
   @end[license]
   @end[doc]
>>

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_subtype
extends Itt_logic
extends Itt_bisect
extends Itt_quotient
extends Itt_ext_equal

doc <:doc< 
   @begin[doc]
   The following rule says that a type is uniquely determined
   by its equality relation.
   @end[doc]
>>

prim eq_mem_eq 'H :
   sequent[squash] {'H; x1: 'X; x2: 'X >- ('x1 = 'x2 in 'A) => ('x1 = 'x2 in 'B)} -->
   sequent['ext] {'H; x: 'A; y: esquash{('x in 'X)} >- 'x in 'B } = it

interactive antiquotient univ[i:l] :
   sequent[squash] {'H >- \subtype{'A; 'B} } -->
   sequent[squash] {'H >- \subtype{'B; . quot x,y: 'A // "true" }} -->
   (* We know A Type, but need explicit univ number *)
   sequent[squash] {'H >- 'A in univ[i:l] } -->
   sequent['ext] {'H >- \subtype{'B ; . quot u,v: 'A // ('u='v in 'B)}}

interactive quotent_isect univ[i:l] :
   [wf] sequent[squash] {'H >- 'A in univ[i:l] } -->
   [wf] sequent[squash] {'H >- "type"{ . quot x,y : 'A //'E1['x;'y]}} -->
   [wf] sequent[squash] {'H >- "type"{ . quot x,y : 'A //'E2['x;'y]}} -->
   [wf] sequent[squash] {'H >- "type"{ . quot x,y : 'A //('E1['x;'y] & 'E2['x;'y])}} -->
   [wf] sequent[squash] {'H; x: 'A; y: 'A >- "type"{'E1['x; 'y]} } -->
   [wf] sequent[squash] {'H; x: 'A; y: 'A >- "type"{'E2['x; 'y]} } -->
   sequent['ext] {'H >- ext_equal{bisect{(quot x,y : 'A //'E1['x;'y]); (quot x,y : 'A //'E2['x;'y])};
                                  (quot x,y : 'A //('E1['x;'y] & 'E2['x;'y])) }}
