(*
 * Homomorphism
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 2002 Xin Yu, Caltech
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
 * Author: Xin Yu
 * Email : xiny@cs.caltech.edu
 *)

extends Czf_itt_group

open Printf
open Mp_debug
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare hom{'g1; 'g2; x. 'f['x]}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * g1 and g2 are groups; f is a map of g1 into g2;
 * and for all a, b in g1, f(a * b) = f(a) * f(b).
 *)
rewrite unfold_hom : hom{'g1; 'g2; x. 'f['x]} <-->
   (group{'g1} & group{'g2} & (all a: set. (mem{'a; car{'g1}} => member{'f['a]; car{'g2}})) & (all a: set. all b: set. (mem{'a; car{'g1}} => mem{'b; car{'g1}} => eq{'a; 'b} => eq{'f['a]; 'f['b]})) & (all a: set. all b: set. (mem{'a; car{'g1}} => mem{'b; car{'g1}} => eq{'f[op{'g1; 'a; 'b}]; op{'g2; 'f['a]; 'f['b]}})))

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Let f: G -> G' be a group homomorphism of G into G'.
 * If e is the identity in G, then f(e) is the identity e' in G'.
 *)
topval homIdT : int -> tactic

(*
 * Let f: G -> G' be a group homomorphism of G into G'.
 * For any a in G, f(inv(a)) = inv(f(a)).
 *)
topval homInvT : term -> int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
