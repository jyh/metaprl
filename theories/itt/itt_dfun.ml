doc <:doc<
   @module[Itt_dfun]

   The @tt[Itt_dfun] module is @emph{derived} from the
   @hrefmodule[Itt_rfun] module.  The type <<x:'A -> 'B['x]>> is
   equivalent to the type $@rfun[x]{f; A; B[x]}$, where $f$ is
   not bound in $B[x]$.  The @emph{well-founded} restriction
   for the very-dependent function type is always trivially satisfied
   (since the range type $B[x]$ never invokes $f$).
   The @tt{Itt_dfun} module derives the dependent-function
   rules.

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
extends Itt_rfun
extends Itt_struct
extends Itt_void
extends Itt_unit
doc docoff

extends Itt_grammar

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_equal
open Itt_subtype
open Itt_rfun

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_dfun%t"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   The @tt[unfold_dfun] gives the definition of the dependent-function space.
>>
prim_rw unfold_dfun : (x: 'A -> 'B['x]) <--> ({ f | x: 'A -> 'B['x] })

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Lemmas}

   The @tt{void_well_founded} rule is a lemma that is
   useful for proving the well-formedness of the
   dependent-function space.  The @hrefterm[void]
   type is trivially well-founded, since it has no elements.
>>
interactive void_well_founded {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- well_founded{'A; a1, a2. void} }

(*
 * @modsubsection{Typehood and equality}
 *
 * The dependent-function space retains the intensional type
 * equality of the very-dependent type.
 *)
interactive functionEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; a1: 'A1 >- 'B1['a1] = 'B2['a1] in univ[i:l] } -->
   sequent { <H> >- (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l] }

(*
 * Typehood.
 *)
interactive functionType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; a: 'A >- "type"{'B['a]} } -->
   sequent { <H> >- "type"{ a:'A -> 'B['a] } }

doc <:doc<
   @modsubsection{Introduction}

   The propositional interpretation of the dependent-function
   is the universal quantification @hrefterm[all], $@all{a; A; B[a]}$.  The
   universal quantification is true, if it is a type,
   and $B[a]$ is true for any $a @in A$.
>>
interactive lambdaFormation {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [main] ('b['z] : sequent { <H>; a: 'A >- 'B['a] }) -->
   sequent { <H> >- a:'A -> 'B['a] }

doc <:doc<
   @modsubsection{Membership}

   The dependent function space contains the @hrefterm[lambda] functions.
>>
interactive lambdaEquality {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; a1: 'A >- 'b1['a1] = 'b2['a1] in 'B['a1] } -->
   sequent { <H> >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in a:'A -> 'B['a] }

doc <:doc<
   @modsubsection{Extensionality}

   The dependent-function retains the extensional membership
   equality of the very-dependent function type.  This rule is
   derived from the @hrefrule[rfunctionExtensionality] rule.
>>
interactive functionExtensionality (y:'C -> 'D['y]) (z:'E -> 'F['z]) :
   [main] sequent { <H>; x: 'A >- ('f 'x) = ('g 'x) in 'B['x] } -->
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'f in y:'C -> 'D['y] } -->
   [wf] sequent { <H> >- 'g in z:'E -> 'F['z] } -->
   sequent { <H> >- 'f = 'g in x:'A -> 'B['x] }

doc <:doc<
   @modsubsection{Elimination}

   The elimination rule @emph{instantiates} the function
   $f@colon <<x:'A -> 'B['x]>>$ with an argument $a @in A$, to
   obtain a proof of $B[a]$. The second form, @tt[independentFunctionElimination],
   is more appropriate for the propositional interpretation of the function
   space <<'A -> 'B>>: if there is a proof of $A$, then there is also a proof
   of $B$.
>>
interactive functionElimination {| elim [] |} 'H 'a :
   [wf] sequent { <H>; f: x:'A -> 'B['x]; <J['f]> >- 'a in 'A } -->
   sequent { <H>; f: x:'A -> 'B['x]; <J['f]>; y: 'B['a]; 'y = ('f 'a) in 'B['a] >- 'T['f] } -->
   sequent { <H>; f: x:'A -> 'B['x]; <J['f]> >- 'T['f] }

interactive independentFunctionElimination 'H :
   [assertion] sequent { <H>; f: 'A -> 'B; <J['f]> >- 'A } -->
   [main] sequent { <H>; f: 'A -> 'B; <J['f]>; y: 'B >- 'T['f] } -->
   sequent { <H>; f: 'A -> 'B; <J['f]> >- 'T['f] }

doc docoff
let d_hyp_fun = argfunT (fun i p ->
   try
      let a = get_with_arg p in
         functionElimination i a
   with
      RefineError _ ->
         independentFunctionElimination i)

let resource elim += (dfun_term, d_hyp_fun)

doc <:doc<
   @modsubsection{Combinator equality}

   Applications have (at least) an @emph{intensional} equality; they are
   equal if their functions and arguments are equal.
>>

interactive applyEquality {| intro[intro_typeinf <<'f1>>; complete_unless_member] |} (x:'A -> 'B['x]) :
   sequent { <H> >- 'f1 = 'f2 in x:'A -> 'B['x] } -->
   sequent { <H> >- 'a1 = 'a2 in 'A } -->
   sequent { <H> >- ('f1 'a1) = ('f2 'a2) in 'B['a1] }

doc docoff

(*
 * Typehood of application depends on the ability to infer a type.
 *)
let d_apply_typeT = funT (fun p ->
   let app = dest_type_term (Sequent.concl p) in
   let f, _ = dest_apply app in
   let f_type =
      try get_with_arg p with
         RefineError _ ->
            infer_type p f
   in
   let tac, univ =
     let _, _, univ = dest_dfun f_type in
         applyEquality, univ
   in
      if is_univ_term univ then
         univTypeT univ thenT tac f_type
      else
         raise (RefineError ("d_apply_typeT", StringTermError ("inferred type is not a univ", univ))))

let resource intro += << "type"{'f 'a} >>, wrap_intro d_apply_typeT

doc <:doc<
   @modsubsection{Subtyping}

   Function spaces are @emph{contravariant} in the domains, and
   @emph{covariant} in their ranges.  More specifically, the
   ranges must be pointwise covariant.

>>
interactive functionSubtype {| intro [] |} :
   ["subtype"] sequent { <H> >- 'A2 subtype 'A1 } -->
   ["subtype"] sequent { <H>; a1: 'A1 >- 'B1['a1] subtype 'B2['a1] } -->
   sequent { <H> >- a1:'A1 -> 'B1['a1]  subtype  a2:'A2 -> 'B2['a2] }
doc docoff

(*
(*
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; J[x] >- T[x]
 * by function_subtypeElimination i
 *
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; y: A2 <= A1; z: a:A2 -> B2[a] <= B1[a]; J[x] >- T[x]
 *)
interactive function_subtypeElimination {| elim [] |} 'H 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent { <H>;
             x: \subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])};
             <J['x]>;
             y: \subtype{'A2; 'A1};
             z: a:'A2 -> \subtype{'B1['a]; 'B2['a]}
             >- 'T['x]
           }) -->
   sequent { <H>; x: \subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])}; <J['x]> >- 'T['x] }
*)

(*
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; J[x] >- T[x]
 * by function_equalityElimination
 *
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; y: A1 = A2 in Ui; z: a:A1 -> B1[a] = B2[a] in Ui; J[x] >- T[x]
interactive function_equalityElimination {| elim [ThinOption thinT] |} 'H 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent { <H>;
             x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l];
             <J['x]>;
             y: 'A1 = 'A2 in univ[i:l];
             z: a:'A1 -> ('B1['a] = 'B2['a] in univ[i:l])
             >- 'T['x]
           }) -->
   sequent { <H>; x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l]; <J['x]> >- 'T['x] }
 *)

(*
 * H >- Ui ext a:A -> B
 * by functionFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
interactive functionFormation 'A :
   [wf] sequent { <H> >- 'A in univ[i:l] } -->
   ('B['a] : sequent { <H>; a: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] }

(************************************************************************
 * EXTENSIOANLITY                                                       *
 ************************************************************************)

(*
 * Takes two arguments.
 *)
let fnExtensionalityT t1 t2 = funT (fun p ->
   let t, _, _ = dest_equal (concl p) in
      if is_fun_term t then
         functionExtensionality t1 t2 thenMT nameHypT (-1) "x"
      else
         functionExtensionality t1 t2)

let fnExtenT t = fnExtensionalityT t t
let fnExtenVoidT = fnExtenT << void -> void >>

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (dfun_term, infer_univ_dep0_dep1 dest_dfun)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let resource sub +=
   (DSubtype ([<< a1:'A1 -> 'B1['a1] >>, << a2:'A2 -> 'B2['a2] >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              functionSubtype))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
