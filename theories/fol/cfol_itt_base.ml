(*
 * Base interpretation of the classical first-order logic.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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
 * jyh@cs.cornell.edu
 *)

extends Itt_theory

derive Fol_type
derive Fol_false
derive Fol_true
derive Fol_pred

open Refiner.Refiner.TermSubst

open Tactic_type
open Tactic_type.Conversionals
open Tactic_type.Tacticals

open Dtactic

open Itt_struct
open Itt_equal

(* Interpretation *)
prim_rw unfold_false : Fol_false!"false" <--> esquash{void}
prim_rw unfold_true : Fol_true!"true" <--> esquash{unit}
prim_rw unfold_type : Fol_type!"type"{'t} <-->
   squash{(('t = "false" in univ[1:l]) or ('t = "true" in univ[1:l]))}
prim_rw unfold_pred : Fol_pred!"pred" <-->
   { T: univ[1:l] | "type"{'T} }

let fold_false = makeFoldC << Fol_false!"false" >> unfold_false
let fold_true = makeFoldC << Fol_true!"true" >> unfold_true
let fold_type = makeFoldC << Fol_type!"type"{'t} >> unfold_type
let fold_pred = makeFoldC << Fol_pred!"pred" >> unfold_pred

(* Lemmas *)
interactive false_univ {| intro [] |} :
   sequent { <H> >- "false" IN univ[1:l] }

interactive true_univ {| intro [] |} :
   sequent { <H> >- "true" IN univ[1:l] }

interactive type_univ :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'A IN univ[1:l] }

let typeT = type_univ

(* Rules for false *)
derived false_type {| intro [] |} :
   sequent { <H> >- "type"{."false"} }

derived false_elim {| elim [] |} 'H :
   sequent { <H>; x: "false"; <J['x]> >- 'C['x] }

(* Rules for true *)
derived true_type {| intro [] |} :
   sequent { <H> >- "type"{."true"} }

derived true_intro {| intro [] |} :
   sequent { <H> >- "true" }

interactive true_concl_elim :
   [main] sequent { <H> >- 'P = "true" in univ[1:l] } -->
   sequent { <H> >- 'P }

interactive true_concl_intro :
   [wf] sequent { <H> >- "type"{'P} } -->
   [main] sequent { <H> >- 'P } -->
   sequent { <H> >- 'P = "true" in univ[1:l] }

let trueT = funT (fun p ->
   let goal = Sequent.concl p in
      if is_equal_term goal then
         true_concl_intro
      else
         true_concl_elim)

(* Rules for pred *)
interactive pred_elim {| elim [] |} 'H :
   sequent { <H>; x: univ[1:l]; y: "type"{'x}; <J['x]> >- 'C['x] } -->
   sequent { <H>; x: pred; <J['x]> >- 'C['x] }

interactive true_pred {| intro [] |} :
   sequent { <H> >- "true" IN pred }

interactive false_pred {| intro [] |} :
   sequent { <H> >- "false" IN pred }

interactive pred_type1 {| intro [] |} :
   sequent { <H> >- Itt_equal!"type"{pred} }

derived pred_type {| elim [] |} 'H :
   sequent { <H>; x: pred; <J['x]> >- "type"{'x} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
