(*
 * We define an equality on sets.
 * The normal intensional equality ('s1 = 's2 in set) is
 * not sufficient, because it is not a small type (it is in U2).
 *
 * We define and extensional equality by induction
 * on the sets.
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
 * Copyright (C) 1998 Jason Hickey, Cornell University
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

include Czf_itt_set

open Refiner.Refiner.TermType

open Tactic_type.Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare eq{'s1; 's2}
declare equal{'s1; 's2}
declare fun_set{z. 'f['z]}
declare fun_prop{z. 'P['z]}
declare dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_eq : eq{'s1; 's2} <-->
   set_ind{'s1; T1, f1, g1.
      set_ind{'s2; T2, f2, g2.
         ((all y1 : 'T1. exst y2: 'T2. eq{.'f1 'y1; .'f2 'y2})
         & (all y2 : 'T2. exst y1: 'T1. eq{.'f1 'y1; .'f2 'y2}))}}

rewrite reduce_eq : eq{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((all y1 : 'T1. exst y2: 'T2. eq{.'f1['y1]; .'f2['y2]})
    & (all y2 : 'T2. exst y1: 'T1. eq{.'f1['y1]; .'f2['y2]}))

rewrite unfold_equal : equal{'s1; 's2} <-->
   ((isset{'s1} & isset{'s2}) & eq{'s1; 's2})

rewrite reduce_equal : equal{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((isset{collect{'T1; x1. 'f1['x1]}} & isset{collect{'T2; x2. 'f2['x2]}})
   & ((all y1 : 'T1. exst y2: 'T2. eq{.'f1['y1]; .'f2['y2]})
     & (all y2 : 'T2. exst y1: 'T1. eq{.'f1['y1]; .'f2['y2]})))

(*
 * A functional predicate can produce proofs for
 * all equal sets.
 *)
rewrite unfold_fun_set : fun_set{z. 'f['z]} <-->
    (all s1: set. all s2: set. (equal{'s1; 's2} => equal{'f['s1]; 'f['s2]}))

rewrite unfold_fun_prop : fun_prop{z. 'P['z]} <-->
    (all s1: set. all s2: set. (equal{'s1; 's2} => 'P['s1] => 'P['s2]))

rewrite unfold_dfun_prop : dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]} <-->
  (all s1: set. all s2: set. (equal{'s1; 's2} => (u1: 'A['s1] -> 'B['s1; 'u1] -> u2: 'A['s2] -> 'B['s2; 'u2])))

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_eq_term : term -> bool
val mk_eq_term : term -> term -> term
val dest_eq : term -> term * term

val is_fun_set_term : term -> bool
val mk_fun_set_term : string -> term -> term
val dest_fun_set : term -> string * term

val is_fun_prop_term : term -> bool
val mk_fun_prop_term : string -> term -> term
val dest_fun_prop : term -> string * term

(*
 * Functionality.
 *)
topval funSetT : int -> tactic

(*
 * Equality relations.
 *)
topval eqSetRefT : tactic
topval eqSetSymT : tactic
topval eqSetTransT : term -> tactic

(*
 * 's1 = 's2 => isset{'s1}
 *)
topval eqSetLeftT : term -> tactic

(*
 * 's1 = 's2 => isset{'s2}
 *)
topval eqSetRightT : term -> tactic

(*
 * Substitution.
 *)
topval setSubstT : term -> int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
