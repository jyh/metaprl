doc <:doc< 
   @begin[doc]
   @module[Dead]
  
   This simple form of dead-code elimination is really easy.
   For any let-definition, let v = a in e, remove the
   let-definition if v is not free in e.
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
  
   @bf{The @Comment!resource[dead_resource]}
  
   The @tt{dead} resource provides a generic method for
   defining @emph{dead code elimination}.  The @conv[deadC] conversion
   can be used to apply this evaluator.
  
   The implementation of the @tt{dead_resource} and the @tt[deadC]
   conversion rely on tables to store the shape of redices, together with the
   conversions for the reduction.
  
   @docoff
   @end[doc]
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
   @modsubsection{Dead-code rewrites}
   @end[doc]
>>
prim_rw dead_let_atom :
   LetAtom{'a; v. 'e} <--> 'e

prim_rw dead_let_tuple :
   LetTuple{'length; 'tuple; v. 'e} <--> 'e

prim_rw dead_let_subscript :
   LetSubscript{'a1; 'a2; v. 'e} <--> 'e

prim_rw dead_let_closure :
   LetClosure{'a1; 'a2; f. 'e} <--> 'e

(* @docoff *)

(*
 * Add all these rules to the dead resource.
 *)
let resource dead +=
    [<< LetAtom{'a; v. 'e} >>, dead_let_atom;
     << LetTuple{'length; 'tuple; v. 'e} >>, dead_let_tuple;
     << LetSubscript{'a1; 'a2; v. 'e} >>, dead_let_subscript;
     << LetClosure{'a1; 'a2; f. 'e} >>, dead_let_closure]

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
