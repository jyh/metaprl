(*!
 * @begin[spelling]
 * axiomFormation squashElimination
 * subtypeElimination info
 * @end[spelling]
 *
 * @begin[doc]
 * @theory[Itt_subtype]
 *
 * The @tt{Itt_subtype} module provides the definition of
 * @emph{subtyping}.  Informally a type $T_1$ is a subtype of
 * a type $T_2$, $T_1 @subseteq T_2$, if any two equal elements of $T_1$ are also
 * equal in $T_2$.  This is slightly different from the set-theoretic
 * definition.  In set theory, the quotiented set $@int_2$ contains
 * two equivalence classes; one is the set of even numbers and the other
 * is the set of odd numbers.  In the @Nuprl{} type theory, the two types
 * have the same elements, but all even numbers are equal in $@int_2$ (and
 * all the odd numbers are also equal).  It follows that $@int @subseteq @int_2$.
 *
 * The subtype-type has trivial computational content, like equality.
 * The subtype contains only the $@it$ term if it is true; it is
 * empty otherwise.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * @email{jyh@cs.caltech.edu}
 *
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Itt_equal
include Itt_struct
include Itt_squash
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Mp_resource
open Term_dtable

open Var

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent

open Base_dtactic

open Itt_equal
open Itt_struct
open Itt_squash

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_subtype%t"

(* debug_string DebugLoad "Loading itt_subtype..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{subtype} term is a binary relation.
 * @end[doc]
 *)
declare subtype{'A; 'B}
(*! @docoff *)

let subtype_term = << subtype{'A; 'B} >>
let subtype_opname = opname_of_term subtype_term
let is_subtype_term = is_dep0_dep0_term subtype_opname
let dest_subtype = dest_dep0_dep0_term subtype_opname
let mk_subtype_term = mk_dep0_dep0_term subtype_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_subtype

dform subtype_df1 : except_mode[src] :: parens :: "prec"[prec_subtype] :: subtype{'A; 'B} =
   slot{'A} `" " subseteq space slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext subtype(A; B)
 * by subtypeFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
prim subtypeFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   subtype{'A; 'B}

(*!
 * @begin[doc]
 * @rules
 *
 * @thysubsection{Typehood and equality}
 *
 * The $<< subtype{'A; 'B} >>$ term is a type if both
 * $A$ and $B$ are types.  The equality is @emph{intensional}:
 * two subtype-types are equal if their subterms are equal.
 * @end[doc]
 *)
prim subtypeEquality {| intro []; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- subtype{'A1; 'B1} = subtype{'A2; 'B2} in univ[i:l] } =
   it

prim subtypeType {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{subtype{'A; 'B}} } =
   it

(*!
 * @begin[doc]
 * The intensional interpretation of typehood also means that if
 * the subtype judgment $A @subseteq B$ is true, then both $A$
 * and $B$ are types.
 * @end[doc]
 *)
prim subtypeTypeLeft 'H 'A :
   [main] sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- "type"{'B} } =
   it

prim subtypeTypeRight 'H 'B :
   [main] sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- "type"{'A} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * The @tt{subtype_axiomFormation} rule gives the introduction form
 * for the subtype judgment.  A type $A @subseteq B$ is true if $A$
 * and $B$ are types, and any term $t @in A$ is also in $B$.  The
 * proof extract term is always the $@it$ term.
 * @end[doc]
 *)
prim subtype_axiomFormation {| intro [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [main] sequent [squash] { 'H; x: 'A >- 'x IN 'B } -->
   sequent ['ext] { 'H >- subtype{'A; 'B} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Member equality}
 * The subtype-type, if true, contains only the term $@it$.
 * For $@it$ to be in $A @subseteq B$, the subtype judgment
 * must be true.
 * @end[doc]
 *)
prim subtype_axiomEquality {| intro []; eqcd; squash |} 'H :
   [main] sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- it IN subtype{'A; 'B} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * Subtype elimination has two forms.  The standard @tt{subtypeElimination}
 * form corresponds to induction: the witness $x@colon A @subseteq B$ is
 * replaced with the unique proof term $@it$.  The second rule
 * @tt{subtypeElimination2} takes a witness $a @in A$ and adds the
 * additional assumption $a @in B$.
 * @end[doc]
 *)
prim subtypeElimination {| elim [ThinOption thinT] |} 'H 'J :
   ('t : sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J['x] >- 'C['x] } =
   't

prim subtypeElimination2 'H 'J 'a 'b 'y :
   [wf] sequent [squash] { 'H; x: subtype{'A; 'B}; 'J['x] >- 'a='b in 'A } -->
   ('t['y] : sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J['x]; y: 'a='b in 'B >- 'C['x] }) -->
   sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J['x] >- 'C['x] } =
   't[it]

(************************************************************************
 * SUBTYPE RESOURCE                                                     *
 ************************************************************************)

type sub_info_type = (term * term) list * tactic

type sub_resource_info =
   LRSubtype of sub_info_type
 | RLSubtype of sub_info_type
 | DSubtype of sub_info_type

(*!
 * @begin[doc]
 * @resources
 *
 * The @tt{Itt_subtype} module defines the @resource[subtype_resource], which is
 * used to prove subtyping judgments.  The @tt{sub_resource_info} argument
 * requires two terms $t_1 @subseteq t_2$ that match the goal term, and
 * a tactic that can be used to refine goals of that form.
 * @end[doc]
 *)
(*! @docoff *)

(*
 * Improve the subtyping information.
 * We are provided with a (term * term) list
 * and a tactic, where the first term pair is the goal, the rest are
 * subgoals, and the supplied tactic should generate the subgoals
 * in order.
 *)
let subtype_f tac subgoals _ =
   let rec aux sg = function
      p::t ->
         let goal = concl p in
            if Opname.eq (opname_of_term goal) subtype_opname then
               match sg with
                  (_, _, tac)::sg' -> (tac p)::(aux sg' t)
                | [] -> raise (RefineError ("subtypeT", StringError "subtype mismatch"))
            else
               (idT p)::(aux sg t)
    | [] -> []
   in
      tac thenFLT aux subgoals

let improve_data base = function
   LRSubtype (goal, tac) ->
      insert_left base goal (subtype_f tac)
 | RLSubtype (goal, tac) ->
      insert_right base goal (subtype_f tac)
 | DSubtype (goal, tac) ->
      insert base goal (subtype_f tac)

(*
 * Extract a subtype tactic from the data.
 * Chain the tactics together.
 *)
let extract_data base =
   let tbl = extract base in
   let subtyper p =
      let t = concl p in
      let t1, t2 = dest_subtype t in
      let tac =
         try lookup tbl t1 t2 with
            Not_found ->
               raise (RefineError ("subtype", StringTermError ("can't infer subtype ", t)))
      in
         tac p
   in
      subtyper

(*
 * Resource.
 *)
let resource sub = Functional {
   fp_empty = empty_dtable;
   fp_add = improve_data;
   fp_retr = extract_data
}

(*
 * Resource argument.
 *)
let prove_subtypeT p =
   Sequent.get_resource_arg p get_sub_resource p

let resource intro +=
   subtype_term, ("prove_subtype",None,prove_subtypeT)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_subtypeT i p =
   let j, k = hyp_indices p i in
   try
      let v, _ = Sequent.nth_hyp p i in
      let v = maybe_new_vars1 p v in
      let args = get_with_args p in
            match args with
              [a] -> subtypeElimination2 j k a a v p |
              [a;b] -> subtypeElimination2 j k a b v p |
              _ -> raise (RefineError ("subtypeElimination", StringError ("1 or 2 arguments required")))
   with RefineError ("get_attribute",_) -> subtypeElimination j k p

let resource elim += (subtype_term, d_hyp_subtypeT)

interactive use_subtype1 'H 'A :
   [aux] sequent [squash] { 'H >- subtype{'A; 'B} } -->
   [main] sequent [squash] { 'H >- 't1 = 't2 in 'A } -->
   sequent ['ext] { 'H >- 't1 = 't2 in 'B }

interactive use_subtype2 'H 'A :
   [aux] sequent [squash] { 'H >- subtype{'A; 'B} } -->
   [main] sequent ['ext] { 'H >- 'A } -->
   sequent ['ext] { 'H >- 'B }

let subtypeT t p =
   let h = Sequent.hyp_count_addr p in
      if is_equal_term (Sequent.concl p) then
         use_subtype1 h t p
      else
         use_subtype2 h t p

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (subtype_term, infer_univ_dep0_dep0 dest_subtype)

(************************************************************************
 * TYPEHOOD FROM SUBTYPE                                                *
 ************************************************************************)

let type_subtype_leftT a p =
   subtypeTypeLeft (Sequent.hyp_count_addr p) a p

let type_subtype_rightT b p =
   subtypeTypeRight (Sequent.hyp_count_addr p) b p

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
