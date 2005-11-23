doc <:doc<
   @module["meta-context-ind1"]
   ``Teleportation'' model of context induction.

   This model is documented more precisely in @code{papers/notebook/context_induction}.

   At a high level, the mechanism works like this.  Suppose we are proving
   a rule @code{S1 --> ... --> Sn(Gamma)} and we wish to do induction on
   Gamma.  For each occurrence of Gamma on which to do induction, specify
   a target location to shift Gamma into.  The target location may be in the
   scope of Gamma, or above the scope of Gamma, but everything in the scope
   of Gamma will remain so.  Then induction works by proving how to move
   Gamma from one location to another.

   For the tactic then, we take a list of source/target addresses.  Each source
   must specify an occurrence of the context variable.  The target must be
   scoped correctly.

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2005 Mojave Group, Caltech

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
extends Meta_implies

doc docoff

open Basic_tactics
open Refiner.Refiner.Refine

(************************************************************************
 * Context induction.
 *)
let context_ind_extract addrs params goal subgoals args rest =
   raise (Invalid_argument "context_ind_extract: not implemented")

let context_ind_code addrs params goal assums =
   let seq = mk_msequent goal assums in
      [seq], context_ind_extract

ml_rule context_ind 't : 'T =
   context_ind_code

(************************************************************************
 * Testing.
 *)

(*
 * Second-order variables are not allowed to occur with
 * more-than one arity.  This means that we can't actually
 * just add the variable in the induction step.  We'll
 * have to invent new variable names.
 *
interactive test1 :
   sequent { <H>; x: 'A >- mimplies{'S; 'S['x]} }
 *)

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
