doc <:doc<
   @begin[doc]
   @module[Itt_fun]

   The @tt[Itt_fun] module defines the non-dependent function type.
   The function type is @emph{derived} from the dependent-function
   type @hrefmodule[Itt_dfun], which is in turn derived from the
   very-dependent function @hrefmodule[Itt_rfun].

   The non-dependent function $@fun{A; B}$ is the type of functions
   with domain $A$, and range $B$.  It is equivalent to the
   dependent function space $@fun{x; A; B}$, where $x$ is not
   bound in $B$.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

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
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_equal
extends Itt_dfun
doc <:doc< @docoff >>

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_equal
open Itt_subtype
open Itt_rfun
open Itt_dfun

extends Itt_prod (* because of FunctionExtensionality *)
open Itt_prod

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_fun%t"

(* debug_string DebugLoad "Loading itt_fun..." *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rewrites

   The non-dependent function $@fun{A; B}$ is defined as the
   dependent function $@fun{x; A; B}$ (where $x$ is new).
   @end[doc]
>>
prim_rw unfold_fun : ('A -> 'B) <--> (x: 'A -> 'B)

doc <:doc< @docoff >>

(************************************************************************
 * Constructors/Destructors                                             *
 ************************************************************************)

let fun_term = <<'A -> 'B>>
let fun_opname = opname_of_term fun_term
let dest_fun = dest_dep0_dep0_term fun_opname
let mk_fun_term = mk_dep0_dep0_term fun_opname

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rules
   @modsubsection{Typehood and equality}

   The non-dependent function has an intensional type equality.
   @end[doc]
>>
interactive independentFunctionEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H> >- 'B1 = 'B2 in univ[i:l] } -->
   sequent { <H> >- ('A1 -> 'B1) = ('A2 -> 'B2) in univ[i:l] }

(*
 * Typehood.
 *)
interactive independentFunctionType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A1} } -->
   [wf] sequent { <H>; x: 'A1 >- "type"{'B1} } -->
   sequent { <H> >- "type"{ 'A1 -> 'B1 } }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction}

   The propositional interpretation of the function space $@fun{A; B}$
   is the implication term @hrefterm[implies], $@implies{A; B}$.
   The proposition is true if it is a type, and for any proof of $A$,
   there is a proof of $B$.
   @end[doc]
>>
interactive independentLambdaFormation {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [main] ('b['z] : sequent { <H>; z: 'A >- 'B }) -->
   sequent { <H> >- 'A -> 'B }

doc <:doc<
   @begin[doc]
   @modsubsection{Membership}

   The elements in the function space $@fun{A; B}$ are the
   @hrefterm[lambda] functions.  The space $@fun{A; B}$ must be a
   type, and the body of the function must be in $B$ for any argument
   in $A$.
   @end[doc]
>>
interactive independentLambdaEquality {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; x: 'A >- 'b1['x] = 'b2['x] in 'B } -->
   sequent { <H> >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in 'A -> 'B }

doc <:doc<
   @begin[doc]
   @modsubsection{Extensionality}

   The independent function retains the extensional membership
   equality of the dependent function type.  This rule is
   derived from the @hrefrule[functionExtensionality] rule.
   @end[doc]
>>
interactive independentFunctionExtensionality ('C -> 'D) ('E -> 'F) :
(*
interactive independentFunctionExtensionality {| intro[intro_typeinf <<'f,'g>>] |} (('C -> 'D)*('E -> 'F)) :
*)
   [main] sequent { <H>; u: 'A >- ('f 'u) = ('g 'u) in 'B } -->
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'f in 'C -> 'D } -->
   [wf] sequent { <H> >- 'g in 'E -> 'F } -->
   sequent { <H> >- 'f = 'g in 'A -> 'B }

interactive independentFunctionExtensionality2 :
   [main] sequent { <H>; u: 'A >- ('f 'u) = ('g 'u) in 'B } -->
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'f in void -> void } -->
   [wf] sequent { <H> >- 'g in void -> void } -->
   sequent { <H> >- 'f = 'g in 'A -> 'B }



doc <:doc<
   @begin[doc]
   @modsubsection{Elimination}

   There are two elimination forms.  The @tt{independentFunctionElimination}
   rule is more appropriate for the propositional interpretation of the function
   space $@fun{A; B}$: if there is a proof of $A$, then there is also a proof
   of $B$.  The second form, @tt{independentFunctionElimination2}, is
   more appropriate for the functional application to a specific argument $a @in A$.
   @end[doc]
>>
interactive independentFunctionElimination 'H :
   [assertion] sequent { <H>; f: 'A -> 'B; <J['f]> >- 'A } -->
   [main] sequent { <H>; f: 'A -> 'B; <J['f]>; y: 'B >- 'T['f] } -->
   sequent { <H>; f: 'A -> 'B; <J['f]> >- 'T['f] }

(*
 * Explicit function elimination.
 *)
interactive independentFunctionElimination2 'H 'a :
   [wf] sequent { <H>; f: 'A -> 'B; <J['f]> >- 'a in 'A } -->
   [main] sequent { <H>; f: 'A -> 'B; <J['f]>; y: 'B; z: 'y = ('f 'a) in 'B >- 'T['f] } -->
   sequent { <H>; f: 'A -> 'B; <J['f]> >- 'T['f] }

interactive independentFunctionEqElimination {| elim[] |} 'H 'a :
   [wf] sequent { <H>; 'f='g in 'A -> 'B; <J> >- 'a in 'A } -->
   [main] sequent { <H>; 'f='g in 'A -> 'B; 'f 'a = 'g 'a in 'B; <J> >- 'T } -->
   sequent { <H>; 'f='g in 'A -> 'B; <J> >- 'T }


doc <:doc<
   @begin[doc]
   @modsubsection{Combinator equality}

   Applications have an intensional equality; they are equal if their
   functions and arguments are equal.
   @end[doc]
>>
interactive independentApplyEquality ('A -> 'B) :
   [wf] sequent { <H> >- 'f1 = 'f2 in 'A -> 'B } -->
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A } -->
   sequent { <H> >- ('f1 'a1) = ('f2 'a2) in 'B }

doc <:doc<
   @begin[doc]
   @modsubsection{Subtyping}

   The function space is @emph{contravariant} in their domains,
   and @emph{covariant} in their ranges.

   @docoff
   @end[doc]
>>
interactive independentFunctionSubtype {| intro [] |} :
   sequent { <H> >- \subtype{'A2; 'A1} } -->
   sequent { <H> >- \subtype{'B1; 'B2} } -->
   sequent { <H> >- \subtype{ ('A1 -> 'B1); ('A2 -> 'B2) } }

(*
 * H >- Ui ext A -> B
 * by independentFunctionFormation
 *
 * H >- Ui ext A
 * H >- Ui ext B
 *)
interactive independentFunctionFormation :
   ('A : sequent { <H> >- univ[i:l] }) -->
   ('B : sequent { <H> >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] }

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * Application equality depends on our infering a type.
 *)
let d_apply_equalT = funT (fun p ->
   let _, app, app' = dest_equal (Sequent.concl p) in
   if
      ((Sequent.get_bool_arg p "d_auto") = (Some true)) &&
      (not (alpha_equal app app'))
   then raise generic_refiner_exn;
   let f, _ = dest_apply app in
   let f_type =
      try get_with_arg p with
         RefineError _ ->
            infer_type p f
   in
   let tac =
      if is_rfun_term f_type then
         rfunction_applyEquality
      else if is_dfun_term f_type then
         applyEquality
      else if is_fun_term f_type then
         independentApplyEquality
      else
         raise (RefineError ("d_apply_equalT", StringTermError ("inferred type is not a function type", f_type)))
   in
      tac f_type)

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
      if is_dfun_term f_type then
         let _, _, univ = dest_dfun f_type in
            applyEquality, univ
      else if is_fun_term f_type then
         independentApplyEquality, snd (dest_fun f_type)
      else
         raise (RefineError ("d_apply_typeT", StringTermError ("inferred type is not a function type", f_type)))
   in
      if is_univ_term univ then
         univTypeT univ thenT tac f_type
      else
         raise (RefineError ("d_apply_typeT", StringTermError ("inferred type is not a univ", univ))))

let resource intro += [
   << 'f1 'a1 = 'f2 'a2 in 'T >>, wrap_intro d_apply_equalT;
   << "type"{'f 'a} >>, wrap_intro d_apply_typeT
]

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_fun = argfunT (fun i p ->
   try
      let a = get_with_arg p in
         independentFunctionElimination2 i a
   with
      RefineError _ ->
         independentFunctionElimination i)

let resource elim += (fun_term, d_hyp_fun)

(************************************************************************
 * EXTENSIOANLITY                                                       *
 ************************************************************************)

(*
 * Takes two arguments.
 *)
let fnExtensionalityT t1 t2 = funT (fun p ->
   if is_rfun_term t1 then
      rfunction_extensionalityT t1 t2
   else if is_dfun_term t1 then
      dfun_extensionalityT t1 t2
   else if is_fun_term t1 then
      let t, _, _ = dest_equal (Sequent.concl p) in
         (* independentFunctionExtensionality <:con<prod{$t1$;$t2$}>> *)
         independentFunctionExtensionality t1 t2
   else raise (RefineError ("extensionalityT", StringTermError ("first arg is not a function type", t1))))

let fnExtenT t = fnExtensionalityT t t


(* BUG: The right way of applying *FunctionExtensionality:
     take C->D, E->F from with or
     let C->D =  typeinf (f) orelse void->void in
     let E->F =  typeinf (g) orelse void->void in
      in  independentFunctionExtensionality C->D E->F
*)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (fun_term, infer_univ_dep0_dep0 dest_fun)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let resource sub +=
   (DSubtype ([<< 'A1 -> 'B1 >>, << 'A2 -> 'B2 >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1 >>, << 'B2 >>],
              independentFunctionSubtype))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
