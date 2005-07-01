doc <:doc<
   @begin[spelling]
   @end[spelling]

   @module[UNITY]
   This module defines a set of abstract language primitives.
   By customizing this module, you can provide the translation
   to another target language.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2003 Adam Granicz, Caltech

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

   Author: Adam Granicz
   @email{granicz@cs.caltech.edu}
   @end[license]
>>
extends Base_theory

extends M_theory

doc <:doc<
   @terms
   Translation operators and helper terms.
>>
declare Source_set{'e1; 'e2; 'cont}
declare Source_if{'e1; 'e2; 'e3; 'cont}

doc <:doc<
   @rewrites
   We provide the meaning of each abstract construct.
>>
(*
prim_rw source_set :
   Source_set{'e1; 'e2; 'cont}
   <-->
*)
(************************************************************************
 * Display forms
 *)

dform source_set_df : Source_set{'e1; 'e2; 'cont} =
   bf["SET "] slot{'e1} bf[" TO "] slot{'e2} hspace slot{'cont}

dform source_if_df : Source_if{'e1; 'e2; 'e3; 'cont} =
   bf["IF "] slot{'e1} bf[" THEN "] slot{'e2} bf[" ELSE "] slot{'e3} hspace slot{'cont}

