(*
 * Kernel of homomorphisms.
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

extends Czf_itt_hom

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

open Dtactic
open Auto_tactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare ker{'h; 'g1; 'g2; x. 'f['x]}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * f is a homomorphism of g1 into g2. The elements of g1,
 * which are mapped into the identity of g2, form a subgroup
 * h of g called the kernel of f.
 *)
rewrite unfold_ker : ker{'h; 'g1; 'g2; x. 'f['x]} <-->
   (hom{'g1; 'g2; x. 'f['x]} & group{'h} & equal{car{'h}; sep{car{'g1}; x. eq{'f['x]; id{'g2}}}} & (all a: set. all b: set. (mem{'a; car{'h}} => mem{'b; car{'h}} => eq{op{'h; 'a; 'b}; op{'g1; 'a; 'b}})))

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Let f: G -> G' be a group homomorphism of G into G'.
 * The kernel of f is a subgroup of G.
 *)
topval kerSubgT : int -> tactic

(*
 * Let f: G1 -> G2 be a group homomorphism of G1 into G2.
 * Let H be the ker of f. For any a in G1, the set
 * { x in G1 | f(x) = f(a) } is the left coset aH of H,
 * and is also the right coset Ha of H.
 *)
topval kerLcosetT : term -> term -> int -> tactic
topval kerRcosetT : term -> term -> int -> tactic

(*
 * The ker of a homomorphism f: G1 -> G2 is a normal subgroup of G1.
 *)
topval kerNormalSubgT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
