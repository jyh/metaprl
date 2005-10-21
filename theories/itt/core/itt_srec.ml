doc <:doc<
   @spelling{unrollings}
   @module[Itt_srec]

   The @tt[Itt_srec] module defines a ``simple'' recursive type,
   without parameters that are passed along the unrollings of the
   type, as it is in the parameterized recursive type in @hrefmodule[Itt_prec].

   The syntax of the recursive type is $@srec{T; B[T]}$.  The variable
   $T$ represents the type itself, which is given through the
   interpretation $T = B[T]$.  The body $B[T]$ must be a type for
   @emph{any} type $T @in @univ{i}$, and in addition $B[T]$ must be
   monotone in the type argument $T$.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998 Jason Hickey, Cornell University

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
   @email{jyh@cs.cornell.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_equal
extends Itt_prec
extends Itt_subtype
extends Itt_void
extends Itt_struct
extends Itt_logic
doc docoff

open Lm_debug
open Lm_symbol
open Lm_printf
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

open Dtactic

open Itt_equal
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_srec%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @terms

   The @tt{srec} term defines the recursive type.  The @tt{srecind}
   term defines an induction combinator over elements of the recursive type.
>>
declare srec{T. 'B['T]}
declare srecind{'a; p, h. 'g['p; 'h]}
doc docoff

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform srec_df : except_mode[src] :: srec{T. 'B} =
   szone mu `"{" slot{'T} `"." pushm[0] slot{'B} `"}" popm ezone

dform srecind_df : except_mode[src] :: srecind{'a; p, h. 'g} =
   szone pushm[3]
   tt["srecind"] `"(" slot{'a} `";" hspace
   slot{'p} `"," slot{'h} `"." hspace
   slot{'g} `")"
   popm ezone

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   The @tt{srecind} induction combinator takes an argument
   $a$ that belongs to a recursive type definition.  The computation
   is defined through the body $g[p, h]$, which takes a
   recursive instance $p$, and the argument element $h$.
>>
prim_rw unfold_srecind : srecind{'a; p, h. 'g['p; 'h]} <-->
   'g[lambda{a. srecind{'a; p, h. 'g['p; 'h]}}; 'a]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @docoff
>>
prim srecFormation :
   ('B['T] : sequent { <H>; T: univ[i:l] >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] } =
   srec{T. 'B['T]}

doc <:doc<
   @rules
   @modsubsection{Typehood and equality}

   The simple recursive type $@srec{T; B[T]}$ is a type if $B[T]$ is
   a monotone type over types type $T @in @univ{i}$.
>>
prim srecEquality {| intro [] |} :
   [wf] sequent { <H>; T: univ[i:l] >- 'B1['T] = 'B2['T] in univ[i:l] } -->
   [wf] sequent { <H>; S1: univ[i:l]; S2: univ[i:l]; z: \subtype{'S1; 'S2} >- \subtype{'B1['S1]; 'B1['S2]} } -->
   sequent { <H> >- srec{T1. 'B1['T1]} = srec{T2. 'B2['T2]} in univ[i:l] } =
   it

interactive srecType {| intro [] |} univ[i:l] :
   [wf] sequent { <H>; T: univ[i:l] >- 'B['T] in univ[i:l] } -->
   [wf] sequent { <H>; S1: univ[i:l]; S2: univ[i:l]; z: \subtype{'S1; 'S2} >- \subtype{'B['S1]; 'B['S2]} } -->
   sequent { <H> >- "type"{srec{T. 'B['T]}} }

doc <:doc<
   @docoff
>>
prim srec_memberFormation {| intro [] |} :
   [wf] ('g : sequent { <H> >- 'B[srec{T. 'B['T]}] }) -->
   [wf] sequent { <H> >- "type"{(srec{T. 'B['T]})} } -->
   sequent { <H> >- srec{T. 'B['T]} } =
   'g

doc <:doc<
   @modsubsection{Membership}

   The elements of the recursive type $@srec{T; B[T]}$ are the
   elements of $B[@srec{T; B[T]}]$.
>>

prim srec_memberEquality {| intro [] |} :
   sequent { <H> >- 'x1 = 'x2 in 'B[srec{T. 'B['T]}] } -->
   [wf] sequent { <H> >- "type"{(srec{T. 'B['T]})} } -->
   sequent { <H> >- 'x1 = 'x2 in srec{T. 'B['T]} } =
   it

doc <:doc<
   @modsubsection{Elimination}

   The elimination form performs induction over the
   assumption $x@colon @srec{T; B[T]}$.  The conclusion $C[x]$ is
   true for the arbitrary element $x$, if, given that it holds on
   the unrollings, it also holds on $x$.
>>

prim srecElimination {| elim [ThinOption thinT] |} 'H univ[i:l] :
   [main] ('g['x; 'T; 'u; 'w; 'z] : sequent {
             <H>;
             x: srec{X. 'B['X]};
             <J['x]>;
             T: univ[i:l];
             u: \subtype{'T; srec{X. 'B['X]}};
             w: all v:'T. 'C['v];
             z: 'B['T]
           >- 'C['z]
           }) -->
   sequent { <H>; x: srec{X. 'B['X]}; <J['x]> >- 'C['x] } =
   srecind{'x; p, h. 'g['x; srec{X. 'B['X]}; it; 'p; 'h]}

doc <:doc<
   The second elimination form performs unrolling of the recursive
   type definition.
>>

prim srecUnrollElimination (* {| elim [ThinOption thinT] |} *) 'H :
   [main] ('g['x; 'y; 'u] : sequent { <H>; x: srec{T. 'B['T]}; <J['x]>; y: 'B[srec{T. 'B['T]}]; u: 'x = 'y in 'B[srec{T. 'B['T]}] >- 'C['y] }) -->
   sequent { <H>; x: srec{T. 'B['T]}; <J['x]> >- 'C['x] } =
   'g['x; 'x; it]

doc <:doc<
   @modsubsection{Combinator equality}

   The @hrefterm[srecind] term produces a value of type $S$ if the
   argument belongs to some recursive type, and the body computes
   a value of type $S$ given the argument $r$ and a function
   $h$ to compute the values of the recursive calls.
>>
prim srecindEquality {| intro [] |} bind{x. 'S['x]} srec{T. 'B['T]} univ[i:l] :
   [wf] sequent { <H> >- 'r1 = 'r2 in srec{T. 'B['T]} } -->
   [wf] sequent { <H>; r: srec{T. 'B['T]} >- "type"{'S['r]} } -->
   [wf] sequent { <H>; T1: univ[i:l]; z: \subtype{'T1; srec{T. 'B['T]}};
               v: w: 'T1 -> 'S['w]; w: 'B['T1]
           >- 't1['v; 'w] = 't2['v; 'w] in 'S['w]
           } -->
   sequent { <H> >- srecind{'r1; h1, z1. 't1['h1; 'z1]}
                   = srecind{'r2; h2, z2. 't2['h2; 'z2]}
                   in 'S['r1]
           } =
   it
doc docoff

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let srec_term = << srec{T. 'B['T]} >>
let srec_opname = opname_of_term srec_term
let is_srec_term = is_dep1_term srec_opname
let dest_srec = dest_dep1_term srec_opname
let mk_srec_term = mk_dep1_term srec_opname

let srecind_term = << srecind{'a; p, h. 'g['p; 'h]} >>
let srecind_opname = opname_of_term srecind_term
let is_srecind_term = is_dep0_dep2_term srecind_opname
let dest_srecind = dest_dep0_dep2_term srecind_opname
let mk_srecind_term = mk_dep0_dep2_term srecind_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of srec.
 *)
let inf_srec inf consts decls eqs opt_eqs defs t =
   let a, body = dest_srec t in
      inf (SymbolSet.add consts a) ((a,univ1_term)::decls) eqs opt_eqs defs body

let resource typeinf += (srec_term, inf_srec)

(*
 * Type of srecind.
 * WRONG according to jyh.
let inf_srecind f decl t =
   let p, h, a, g = dest_srecind t in
   let decl', a' = f decl a in
      f (eqnlist_append_var_eqn p a' (eqnlist_append_var_eqn h a' decl')) g

let resource typeinf += (srecind_term, inf_srecind)
*)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)


(* BUG: There are some questions about srec. This theory is subject to be changed.
   1. Is the rule srecType valid?

     Suppose we have B: U_n -> U_{n+1}, but not in U_n->U_n.
     Or we have B:U_2->U_2, s.t. B is monotone on U_1, but not on U_2.
     The rule allow us to form  srec{T. B[T]}, but I don't see semantics for this type.

     I think this rule should have additiona assumption: B: U_i -> U_i.

   2. Even if we add this assumption. Would the rule srecElimination be valid?

     Suppose  we have  B: U_2 -> U_2, s.t. B is monotone on U_2, but B is not in U_1 -> U_1.
     Then would an apllication of rule srecElimination <<univ[1:l]>> be valid?
     I don't think so.
     It means that we have to define srec[i:l]{T.B[T]}


   3. Om the other hand I want to ba able to constract rec{T.B(T)} even if B is monotone  U_i[A] -> U_i[A]
   (where U_i[A] = {X:U_i|X < A}), but not nessecry from Ui->Ui. Semanticly it makes sence, but current rules do not allow that.

*)
