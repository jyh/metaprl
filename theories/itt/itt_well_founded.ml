(*!
 * @begin[doc]
 * @theory[Itt_well_founded]
 *
 * The @tt{Itt_well_founded} module provides a more convenient
 * description of well-foundness than the @hrefterm[well_founded_prop]
 * term formalized in the @hreftheory[Itt_rfun] module.  The definition
 * of well-foundness requires the derivation of an induction
 * principle.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1999 Jason Hickey, Cornell University
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
 * @email{jyh@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Itt_fun
include Itt_logic

open Base_dtactic

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{partial_order} term specifies that $R$ is a partial
 * order on type $A$.  The @tt{well_founded} term specifies that,
 * in addition, $R$ is a well-founded order on $A$.
 *
 * The definition of @tt{partial_order} is that the order is
 * anti-reflexive, anti-symmetric, and transitive.
 *
 * The definition of @tt{well_founded} requires that $R$ be a partial
 * order, and that there is an @emph{induction} principle that can be
 * used to prove any predicate $P$ on $A$.  This is different from the
 * classical definition (that there are no infinite descending chains),
 * but the induction principle implies that classical property.
 * @end[doc]
 *)
define unfold_partial_order : partial_order{'A; x, y. 'R['x; 'y]} <-->
   ((all x: 'A. "not"{'R['x; 'x]})
    & (all x: 'A. all y: 'A. ('R['x; 'y] => "not"{'R['y; 'x]}))
    & (all x: 'A. all y: 'A. all z: 'A. ('R['x; 'y] => ('R['y; 'z] => 'R['x; 'z]))))

define unfold_well_founded : well_founded[i:l]{'A; x, y. 'R['x; 'y]} <-->
   (partial_order{'A; x, y. 'R['x; 'y]}
    & (all P: ('A -> univ[i:l]).
       ((all x: 'A. ((all y: 'A. ('R['y; 'x] => ('P 'y))) => ('P 'x))) =>
        (all x: 'A. 'P 'x))))
(*! @docoff *)

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform partial_order_df : except_mode[src] :: partial_order{'A; x, y. 'R} =
   szone `"partial_order(" pushm[3] slot{'x} `"," slot{'y} `":" slot{'A} `"." hspace slot{'R} `")" popm ezone

dform well_founded_df : except_mode[src] :: well_founded[i:l]{'A; x, y. 'R} =
   szone `"well_founded[" slot[i:l] `"](" pushm[3] slot{'x} `"," slot{'y} `":" slot{'A} `"." hspace slot{'R} `")" popm ezone

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Well-formedness}
 *
 * The @tt{partial_order} and @tt{well_founded} predicates are
 * both well-formed if their domain $A$ is a type, and their
 * relation $R$ is a binary relation.
 * @end[doc]
 *)
interactive partial_order_type {| intro [] |} 'H 'a 'b :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; a: 'A; b: 'A >- "type"{'R['a; 'b]} } -->
   sequent ['ext] { 'H >- "type"{partial_order{'A; x, y. 'R['x; 'y]}} }

interactive well_founded_type {| intro [] |} 'H 'a 'b :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; a: 'A; b: 'A >- "type"{'R['a; 'b]} } -->
   sequent ['ext] { 'H >- "type"{well_founded[i:l]{'A; x, y. 'R['x; 'y]}} }

(*!
 * @begin[doc]
 * The purpose of this definition is to give a more convenient
 * specification of well-foundness that uses normal quantification
 * in its formalization (the @hrefterm[well_founded_prop] predicate defined
 * in the @hreftheory[Itt_rfun] can't use the function type in its
 * definition).  The following rule specifies that the new
 * description of well-foundness is sufficient to derive the
 * primitive definition.
 * @end[doc]
 *)
interactive well_founded_reduction 'H 'a 'b univ[i:l] :
   [wf] sequent [squash] { 'H >- 'A IN univ[i:l] } -->
   [wf] sequent [squash] { 'H; a: 'A; b: 'A >- 'R['a; 'b] IN univ[i:l] } -->
   [main] sequent ['ext] { 'H >- well_founded[i:l]{'A; x, y. 'R['x; 'y]} } -->
   sequent ['ext] { 'H >- Itt_rfun!well_founded{'A; x, y. 'R['x; 'y]} }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
