doc <:doc<
   @module[Itt_disect]

   The @tt[Itt_disect] module defines the @emph{dependent intersection}
   type $@bisect{x@colon A; B[x]}$.
   This type contains all elements $a$ from $A$ such that $a$ is also
   in $B[a]$.

   For example if $A=@int$ and $B[x]=@set{y;@int;y>2*y}$
   then $@bisect{x@colon A; B[x]}$ contains all integers,
   such that $x>2*x$.

   Do not confuse dependent intersection with $@isect{x;A;B[x]}$ defined
   in the @hrefmodule[Itt_isect] theory.
   The latter type refers to the intersection of a family of types.

   In some sense the dependent intersection is similar to
   the dependent product type $@prod{x;A;B[x]}$
   (when $@isect{x;A;B[x]}$ is similar to the function space
   <<x:'A -> 'B['x]>>).

   The ordinary binary intersection can be defined just as dependent
   intersection with a constant second argument:
   $@bisect{A;B}=@bisect{x@colon A;B}$.

   Dependent intersection is used to represent @emph{dependent} records.
   For example the record
   $@record{{@tt[x]@colon A;@tt[y]@colon B[@tt[x]]}}$
   can be defined as
   $@bisect{x@colon @record{@tt[x]@colon A};@record{B[x.@tt[x]]}}$

   Sets also can be defined as dependent intersection
   $@set{x;A;P[x]} = @bisect{x@colon A;squash(P[x])}$

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

   Author: Alexei Kopylov
   @email{kopylov@cs.cornell.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>

extends Itt_equal
extends Itt_dfun
extends Itt_set
extends Itt_isect
extends Itt_tsquash
extends Itt_subtype
extends Itt_ext_equal
doc docoff

open Lm_debug
open Lm_printf
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Tacticals

open Dtactic

open Perv
open Itt_equal
open Itt_subtype
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_disect%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @terms

   The @tt{disect} term denotes the dependent intersection type.
>>

declare bisect{'A; x. 'B['x]}

doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform disect_df1 : except_mode[src] :: (bisect{'A; x.'B}) =
   slot{'x} `":" slot{'A} cap slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext disect x: A. B[x]
 * by dintersectionFormation A
 * H >- A = A in Ui
 * H, x: A >- Ui ext B[x]
 *)
prim dintersectionFormation 'A :
   [wf] sequent { <H> >- 'A = 'A in univ[i:l] } -->
   ('B['x] : sequent { <H>; x: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] } =
   bisect{'A; x.'B['x]}

doc <:doc<
   @rules
   @modsubsection{Typehood and equality}

   The intersection $@bisect{x@colon A; B[x]}$ is well-formed if
   $A$ is a type, and $B[x]$ is a family of types indexed by
   $x @in A$.
>>

prim dintersectionEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent { <H> >- bisect{'A1; x1.'B1['x1]} = bisect{'A2; x2.'B2['x2]} in univ[i:l] } =
   it

prim dintersectionType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- "type"{bisect{'A; x. 'B['x]}} } =
   it

prim dintersectionTypeElimination {| elim [ThinOption thinT] |} 'H 'a :
   [wf] sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; <J['u]>  >- 'a in 'A } -->
   ('t['u;'v] :
   sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; v:"type"{'B['a]}; <J['u]> >- 'C['u] }) -->
   sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; <J['u]> >- 'C['u] } =
   't['u;it]

doc <:doc<
   @modsubsection{Membership}
   Two elements $t1$ and $t2$ are equal in $@bisect{x@colon A; B[x]}$ if
   they are equal both in $A$ and in $B[t1]$.
   That is $t @in @bisect{x@colon A; B[x]}$ if $t @in A$ and $t @in B[t]$.
>>

prim dintersectionMemberEquality {| intro [] |} :
   [wf] sequent { <H>; x:'A >- "type"{'B['x]} } -->
   sequent { <H> >- 't1 = 't2 in 'A } -->
   sequent { <H> >- 't1 = 't2 in 'B['t1] } -->
   sequent { <H> >- 't1 = 't2 in bisect{'A; x.'B['x]} } =
   it

doc <:doc<
   @modsubsection{Introduction}
   There is no special rule for introduction.
   The only one way to introduce dependent intersection is to present
   its witness @emph{explicitly} and use the above rule.
>>

interactive dintersectionMemberFormation {| intro [] |} 't:
   [wf] sequent { <H>; x:'A >- "type"{'B['x]} } -->
   sequent { <H> >- 't in 'A } -->
   sequent { <H> >- 't in 'B['t] } -->
   sequent { <H> >- bisect{'A; x.'B['x]} }

doc <:doc<
   @modsubsection{Elimination}
   The elimination rule for an assumption $x@colon @bisect{y@colon A;B[y]}$
   produces two witnesses that $x @in A$ and that $x @in B[x]$
>>

prim disectElimination {| elim [] |} 'H  bind{a,b.'T['a;'b]}:
   [main] ('t['x; 'a; 'b] :
   sequent { <H>; x: bisect{'A; y.'B['y]}; <J['x]>;  a:'A; b: 'B['a]  >- 'T['a;'b] }) -->
   sequent { <H>; x: bisect{'A; y.'B['y]}; <J['x]> >- 'T['x;'x] } =
   't['x; 'x; 'x]

doc <:doc<
   As a corollary of elimination rule we have that if
   two terms are equal in dependent intersection, they are also
   equal in both cases of the intersection.
   The @tactic[disectCaseEqualityT] applies this rule
>>

interactive disectMemberCaseEquality1 (bisect{'A;x.'B['x]}) :
   [wf] sequent { <H> >- 'x1 = 'x2 in bisect{'A; y.'B['y]}  } -->
   sequent { <H> >- 'x1 = 'x2 in 'A }

interactive disectMemberCaseEquality2 (bisect{'A;x.'B['x]}) :
   [wf] sequent { <H> >- 'x1 = 'x2 in bisect{'A; y.'B['y]}  } -->
   sequent { <H> >- 'x1 = 'x2 in 'B['x1] }

doc docoff

let disectCaseEqualityT t =
   disectMemberCaseEquality2 t orelseT disectMemberCaseEquality1 t

(* disectElimination_eq is derived from disectMemberCaseEquality1/2
   (with the help of dintersectionTypeElimination).
   Therefore we can state disectMemberCaseEquality1/2 as primitive.
   Note that in pairwise functionality we do not need dintersectionTypeElimination
   to derive disectElimination_eq.
*)

interactive disectElimination_eq {| elim [] |} 'H bind{x.bind{a,b.'C['x;'a;'b]}} :
   [main] sequent { <H>; x: bisect{'A; y.'B['y]}; <J['x]>;
                           a: 'A; u: 'a = 'x in 'A; b: 'B['a]; v: 'b = 'x in 'B['a]  >- 'C['x;'a;'b] } -->
   sequent { <H>; x: bisect{'A; y.'B['y]}; <J['x]> >- 'C['x;'x;'x] }

let disectEliminationT = argfunT (fun n p ->
   let x = Sequent.nth_binding p n in
   let bind =  get_with_arg p in
      if is_bind2_term bind then
         let bind = mk_bind1_term x bind in
            disectElimination_eq n bind
      else
         raise (RefineError
           ("disectElimination", StringTermError ("required the bind term:",<<bind{a,b.'C['a;'b]}>>))))

let disectEliminationT = argfunT (fun n p ->
   let n = Sequent.get_pos_hyp_num p n in
      disectEliminationT n thenT thinIfThinningT [-3;-1;n])

let resource elim += (<<bisect{'A; x.'B['x]}>>, wrap_elim disectEliminationT)

doc <:doc<

   The elimination rule has also two simpler forms.
   The first produces a witness $a$ for $A$, and the second produces two witness $a$ for $A$
   and $b$ for $B[a]$.
>>

interactive disectEliminationLeft (*{| elim [SelectOption 1] |}*) 'H :
   sequent { <H>; x: bisect{'A; y.'B['y]}; <J['x]>;
                    a: 'A; u: 'a = 'x in 'A;  b: 'B['a]; v: 'b = 'x in 'B['a] >- 'C['a] } -->
   sequent { <H>; x: bisect{'A; y.'B['y]}; <J['x]> >- 'C['x] }

interactive disectEliminationRight (*{| elim [SelectOption 2] |}*) 'H :
   sequent { <H>; x: bisect{'A; y.'B['y]}; <J['x]>;
                    a: 'A; u: 'a = 'x in 'A;  b: 'B['a]; v: 'b = 'x in 'B['a] >- 'C['b] } -->
   sequent { <H>; x: bisect{'A; y.'B['y]}; <J['x]> >- 'C['x] }

doc docoff

let disectEliminationT = argfunT (fun n p ->
   let n = Sequent.get_pos_hyp_num p n in
   match get_sel_arg p with
      None -> disectEliminationT n
    | Some 1 -> disectEliminationLeft n thenT thinIfThinningT [-3;-1;n]
    | Some 2 -> disectEliminationRight n thenT thinIfThinningT [-3;-1;n]
    | Some _ -> raise (RefineError ("disectElimination", StringError ("select option is out of range ([1,2])"))))

let resource elim += (<<bisect{'A; x.'B['x]}>>, wrap_elim disectEliminationT)

doc <:doc<
   @modsubsection{Subtyping}

   The dependent intersection $@bisect{x@colon A; B[x]}$ is covariant
   in both $A$ and $B[x]$.
>>

interactive dintersectionSubtype :
   ["subtype"] sequent { <H> >- 'A1 subtype 'A2 }  -->
   ["wf"] sequent { <H>; a: 'A2 >- "type"{'B2['a]} } -->
   ["subtype"] sequent { <H>; a: 'A1 >- 'B1['a] subtype 'B2['a]} -->
   sequent { <H> >- bisect{'A1; a1.'B1['a1]} subtype bisect{'A2; a2.'B2['a2]} }

(************************************************************************
 * INTERACTIVE RULES                                                    *
 ************************************************************************)

interactive dinter_associativity :
   [wf] sequent{ <H> >- "type"{'A}} -->
   [wf] sequent{ <H>; a:'A >- "type"{'B['a]}} -->
   [wf] sequent{ <H>; a:'A; b:'B['a] >- "type"{'C['a;'b]}} -->
   sequent { <H> >- ext_equal{
                       bisect{'A;a.bisect{'B['a];b.'C['a;'b]}};
                       bisect{bisect{'A;a.'B['a]};ab.'C['ab;'ab]}
                  }}

doc <:doc<
   @modsubsection{Set type as dependent intersection}

   As an example of using dependent intersection we show that
   sets (@hrefmodule[Itt_set]) are extensionally equal to dependent intersections.

   First let us define $[A]$ as $@set{x;Top;A}$.
>>

doc <:doc<
   Now we can prove that
   $@set{x;A;P[x]} = @bisect{x@colon A;[P[x]]}$
>>

interactive set_is_disect {| intro [] |} :
   [wf] sequent{ <H> >- "type"{'A}} -->
   [wf] sequent{ <H>; x:'A >- "type"{'P['x]}} -->
   sequent { <H> >- ext_equal{ {x: 'A | 'P['x]}; bisect{'A;x.tsquash{'P['x]}}}}

doc docoff

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let disect_term = << bisect{'A; x.'B['x]} >>
let disect_opname = opname_of_term disect_term
let is_disect_term = is_dep0_dep1_term disect_opname
let dest_disect = dest_dep0_dep1_term disect_opname
let mk_disect_term = mk_dep0_dep1_term disect_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (disect_term, infer_univ_dep0_dep1 dest_disect)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two intersection types.
 *)
let resource sub +=
   (DSubtype ([<< bisect{'A1; a1.'B1['a1]} >>, << bisect{'A2; a2.'B2['a2]} >>;
               << 'A1 >>, << 'A2 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              dintersectionSubtype))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
