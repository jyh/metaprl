doc <:doc<
   @begin[spelling]
   redeces
   @end[spelling]

   @begin[doc]
   @module[M_dead]

   This module implements an aggressive form of dead-code elimination.
   A let-definition is considered dead if the variable it defines is not
   used.  If the defining value would normally raise an exception (e.g.,
   division by zero), the semantics of the program could change.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2003 Jason Hickey, Caltech

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
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends M_ir
doc <:doc< @docoff >>

open M_ir
open M_util

open Refiner.Refiner.Term

open Mp_resource
open Term_match_table

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

(************************************************************************
 * Resource.
 *)

doc <:doc<
   @begin[doc]
   @resources

   The @tt{dead} resource provides a generic method for
   defining @emph{dead code elimination}.  The @conv[deadC] conversion
   can be used to apply this evaluator.

   The implementation of the @tt{dead_resource} and the @tt[deadC]
   conversion rely on tables to store the shape of redices, together with the
   conversions for the reduction.

   @end[doc]
   @docoff
>>
let resource dead =
   table_resource_info identity extract_data

let deadTopC_env e =
   get_resource_arg (env_arg e) get_dead_resource

let deadTopC = funC deadTopC_env

let deadC =
   repeatC (higherC deadTopC)

(************************************************************************
 * Rewrites.
 *)

doc <:doc<
   @begin[doc]
   @rewrites

   The rewrites are straightforward.  Note that in the redeces below, $v$ is
   not allowed to be free in $e$.  Each of these rewrites is added to the
   @tt{dead_resource}.
   @end[doc]
>>
prim_rw dead_let_atom :
   LetAtom{'a; v. 'e} <--> 'e

prim_rw dead_let_tuple :
   LetTuple{'length; 'tuple; v. 'e} <--> 'e

prim_rw dead_let_subscript :
   LetSubscript{'a1; 'a2; v. 'e} <--> 'e

prim_rw dead_let_closure :
   LetClosure{'a1; 'a2; v. 'e} <--> 'e

doc <:doc< @docoff >>

(*
 * Add all these rules to the dead resource.
 *)
let resource dead +=
    [<< LetAtom{'a; v. 'e} >>, dead_let_atom;
     << LetTuple{'length; 'tuple; v. 'e} >>, dead_let_tuple;
     << LetSubscript{'a1; 'a2; v. 'e} >>, dead_let_subscript;
     << LetClosure{'a1; 'a2; v. 'e} >>, dead_let_closure]

(*
 * Top-level tactic.
 *)
let deadT =
   onAllHypsT (fun i -> tryT (rw deadC i)) thenT rw deadC 0

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
