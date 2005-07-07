doc <:doc<
   @spelling{klein}

   @module[Czf_itt_kleingroup]

   The @tt[Czf_itt_kleingroup] module defines the klein 4-group, which
   contains 4 elements $e$, $a$, $b$, $c$, and whose group table is:

   $$
      @space @space @space @space | @space e @space a @space b @space c
   $$
   $$
      --|----
   $$
   $$
      @space @space e @space | @space e @space a @space b @space c
   $$
   $$
      @space @space a @space | @space a @space e @space c @space b
   $$
   $$
      @space @space b @space | @space b @space c @space e @space a
   $$
   $$
      @space @space c @space | @space c @space b @space a @space e
   $$

(*    @space @space @space @space @space @space @space   | $e$ $a$ $b$ $c$

      @space @space @space @space----|-----------------

      @space @space @space @space @space $e$ @space | $e$ $a$ $b$ $c$

      @space @space @space @space @space $a$ @space | $a$ $e$ $c$ $b$

      @space @space @space @space @space $b$ @space | $b$ $c$ $e$ $a$

      @space @space @space @space @space $c$ @space | $c$ $b$ $a$ $e$
*)
   The klein 4-group is assigned a label $@klein4$. Its carrier set,
   operation, identity, and inverse are all rewritten in terms of
   its elements $@k0$, $@k1$, $@k2$, and $@k3$. By showing all the
   axioms for groups are satisfied, we prove that $@klein4$ is a group.
   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2002 Xin Yu, Caltech

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

   Author: Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Czf_itt_group
extends Czf_itt_singleton
extends Czf_itt_union
doc docoff

open Lm_debug
open Lm_printf

open Dtactic

let _ =
   show_loading "Loading Czf_itt_kleingroup%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc terms
declare klein4          (* The label representing the klein 4-group *)
declare k0              (* Identity of the group *)
declare k1              (* Element of the group *)
declare k2              (* Element of the group *)
declare k3              (* Element of the group *)
doc docoff

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   The definition of the klein 4-group.
>>
prim_rw unfold_klein4_car : car{klein4} <-->
   union{sing{k0}; union{sing{k1}; union{sing{k2}; sing{k3}}}}
prim_rw unfold_klein4_op00 : op{klein4; k0; k0} <--> k0
prim_rw unfold_klein4_op01 : op{klein4; k0; k1} <--> k1
prim_rw unfold_klein4_op02 : op{klein4; k0; k2} <--> k2
prim_rw unfold_klein4_op03 : op{klein4; k0; k3} <--> k3
prim_rw unfold_klein4_op10 : op{klein4; k1; k0} <--> k1
prim_rw unfold_klein4_op11 : op{klein4; k1; k1} <--> k0
prim_rw unfold_klein4_op12 : op{klein4; k1; k2} <--> k3
prim_rw unfold_klein4_op13 : op{klein4; k1; k3} <--> k2
prim_rw unfold_klein4_op20 : op{klein4; k2; k0} <--> k2
prim_rw unfold_klein4_op21 : op{klein4; k2; k1} <--> k3
prim_rw unfold_klein4_op22 : op{klein4; k2; k2} <--> k0
prim_rw unfold_klein4_op23 : op{klein4; k2; k3} <--> k1
prim_rw unfold_klein4_op30 : op{klein4; k3; k0} <--> k3
prim_rw unfold_klein4_op31 : op{klein4; k3; k1} <--> k2
prim_rw unfold_klein4_op32 : op{klein4; k3; k2} <--> k1
prim_rw unfold_klein4_op33 : op{klein4; k3; k3} <--> k0
prim_rw unfold_klein4_id   : id{klein4} <--> k0
prim_rw unfold_klein4_inv0 : inv{klein4; k0} <--> k0
prim_rw unfold_klein4_inv1 : inv{klein4; k1} <--> k1
prim_rw unfold_klein4_inv2 : inv{klein4; k2} <--> k2
prim_rw unfold_klein4_inv3 : inv{klein4; k3} <--> k3
doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform klein4_df : except_mode[src] :: klein4 =
   `"klein4"

dform k0_df : except_mode[src] :: k0 =
   `"k0"

dform k1_df : except_mode[src] :: k1 =
   `"k1"

dform k2_df : except_mode[src] :: k2 =
   `"k2"

dform k3_df : except_mode[src] :: k3 =
   `"k3"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Well-formedness}

   The @tt[klein4] is a label and @tt[k0], @tt[k1], @tt[k2], @tt[k3]
   are all sets. These are axioms.
>>
prim klein4_label {| intro [] |} :
   sequent { <H> >- klein4 IN label } = it

prim k0_isset {| intro [] |} :
   sequent { <H> >- isset{k0} } = it

prim k1_isset {| intro [] |} :
   sequent { <H> >- isset{k1} } = it

prim k2_isset {| intro [] |} :
   sequent { <H> >- isset{k2} } = it

prim k3_isset {| intro [] |} :
   sequent { <H> >- isset{k3} } = it

doc <:doc<

   The $@car{@klein4}$, $@id{@klein4}$ are well-formed; the
   $@op{@klein4; s_1; s_2}$ is well-formed if its set
   arguments are both sets; the $@inv{@klein4; s}$ is
  well-formed if its set argument is a set.
>>
interactive klein4_car_isset {| intro[] |} :
   sequent { <H> >- isset{car{klein4}} }

interactive klein4_op_isset {| intro[] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- isset{op{klein4; 's1; 's2}} }

interactive klein4_id_isset {| intro [] |} :
   sequent { <H> >- isset{id{klein4}} }

interactive klein4_inv_isset {| intro[] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- isset{inv{klein4; 's1}} }

doc <:doc<
   @modsubsection{Introduction and elimination for the carrier set}

   The $@car{@klein4}$ contains $@k0$, $@k1$, $@k2$, $@k3$ only.
>>
interactive car_klein0 {| intro[] |} :
   sequent { <H> >- mem{k0; car{klein4}} }

interactive car_klein1 {| intro[] |} :
   sequent { <H> >- mem{k1; car{klein4}} }

interactive car_klein2 {| intro[] |} :
   sequent { <H> >- mem{k2; car{klein4}} }

interactive car_klein3 {| intro[] |} :
   sequent { <H> >- mem{k3; car{klein4}} }

interactive car_klein0_elim {| elim [] |} 'H :
   sequent { <H>; x: mem{'y; car{klein4}}; <J['x]> >- isset{'y} } -->
   sequent { <H>; x: mem{'y; car{klein4}}; <J['x]>; z: eq{'y; k0} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; car{klein4}}; <J['x]>; z: eq{'y; k1} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; car{klein4}}; <J['x]>; z: eq{'y; k2} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; car{klein4}}; <J['x]>; z: eq{'y; k3} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; car{klein4}}; <J['x]> >- 'T['x] }

doc <:doc<
   @modsubsection{Verification of the group axioms}

   The @tt[op] for @tt[klein4] is functional and is a mapping.
>>
interactive klein4_op_fun {| intro[] |} :
   sequent { <H> >- fun_set{z. 's1['z]} } -->
   sequent { <H> >- fun_set{z. 's2['z]} } -->
   sequent { <H> >- fun_set{z. op{klein4; 's1['z]; 's2['z]}} }

interactive klein4_op_closure {| intro[] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'s1; car{klein4}} } -->
   sequent { <H> >- mem{'s2; car{klein4}} } -->
   sequent { <H> >- mem{op{klein4; 's1; 's2}; car{klein4}} }
doc docoff

interactive klein4_op_eq1 {| intro[] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- isset{'s3} } -->
   sequent { <H> >- mem{'s1; car{klein4}} } -->
   sequent { <H> >- mem{'s2; car{klein4}} } -->
   sequent { <H> >- mem{'s3; car{klein4}} } -->
   sequent { <H> >- eq{'s1; 's2} } -->
   sequent { <H> >- eq{op{klein4; 's3; 's1}; op{klein4; 's3; 's2}} }

interactive klein4_op_eq2 {| intro[] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- isset{'s3} } -->
   sequent { <H> >- mem{'s1; car{klein4}} } -->
   sequent { <H> >- mem{'s2; car{klein4}} } -->
   sequent { <H> >- mem{'s3; car{klein4}} } -->
   sequent { <H> >- eq{'s1; 's2} } -->
   sequent { <H> >- eq{op{klein4; 's1; 's3}; op{klein4; 's2; 's3}} }

doc <:doc<

   The @tt[op] for @tt[klein4] is associative.
>>
interactive klein4_op_assoc1 {| intro[] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- isset{'s3} } -->
   sequent { <H> >- mem{'s1; car{klein4}} } -->
   sequent { <H> >- mem{'s2; car{klein4}} } -->
   sequent { <H> >- mem{'s3; car{klein4}} } -->
   sequent { <H> >- eq{op{klein4; op{klein4; 's1; 's2}; 's3}; op{klein4; 's1; op{klein4; 's2; 's3}}} }
doc docoff

interactive klein4_op_assoc2 {| intro[] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- isset{'s3} } -->
   sequent { <H> >- mem{'s1; car{klein4}} } -->
   sequent { <H> >- mem{'s2; car{klein4}} } -->
   sequent { <H> >- mem{'s3; car{klein4}} } -->
   sequent { <H> >- eq{op{klein4; 's1; op{klein4; 's2; 's3}}; op{klein4; op{klein4; 's1; 's2}; 's3}} }

doc <:doc<

   The axioms for the identity are satisfied.
>>
interactive klein4_id_mem {| intro[] |} :
   sequent { <H> >- mem{id{klein4}; car{klein4}} }

interactive klein4_id_eq1 {| intro[] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- mem{'s; car{klein4}} } -->
   sequent { <H> >- eq{op{klein4; id{klein4}; 's}; 's} }

doc <:doc<

   The axioms for the inverse are satisfied.
>>
interactive klein4_inv_fun {| intro[] |} :
   sequent { <H> >- fun_set{z. inv{klein4; 'z}} }

interactive klein4_inv_mem {| intro[] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- mem{'s1; car{klein4}} } -->
   sequent { <H> >- mem{inv{klein4; 's1}; car{klein4}} }

interactive klein4_inv_id1 {| intro[] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- mem{'s1; car{klein4}} } -->
   sequent { <H> >- eq{op{klein4; inv{klein4; 's1}; 's1}; id{klein4}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
