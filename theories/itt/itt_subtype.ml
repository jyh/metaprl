doc <:doc<
   @begin[doc]
   @module[Itt_subtype]

   The @tt[Itt_subtype] module provides the definition of
   @emph{subtyping}.  Informally, a type $T_1$ is a subtype of
   a type $T_2$, <<'T_1 subtype 'T_2>>, if any two equal elements of $T_1$ are also
   equal in $T_2$.  This is slightly different from the set-theoretic
   definition.  In set theory, the quotiented set $@int_2$ contains
   two equivalence classes; one is the set of even numbers and the other
   is the set of odd numbers.  In the @Nuprl type theory, the two types
   have the same elements, but all even numbers are equal in $@int_2$ (and
   all the odd numbers are also equal).  It follows that
   << (<:doc<@int>>) subtype (<:doc< @int_2 >>) >>.

   The subtype-type has trivial computational content, like equality.
   The subtype contains only the <<it>> term if it is true; it is
   empty otherwise.
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
   @email{jyh@cs.caltech.edu}

   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_equal
extends Itt_struct
extends Itt_squash
doc <:doc< @docoff >>

open Lm_debug
open Lm_printf

open Basic_tactics
open Term_dtable

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

doc <:doc<
   @begin[doc]
   @terms

   The @tt{subtype} term is a binary relation.
   @end[doc]
>>
declare \subtype{'A; 'B}
doc <:doc< @docoff >>

let subtype_term = << 'A subtype 'B >>
let subtype_opname = opname_of_term subtype_term
let is_subtype_term = is_dep0_dep0_term subtype_opname
let dest_subtype = dest_dep0_dep0_term subtype_opname
let mk_subtype_term = mk_dep0_dep0_term subtype_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_subtype

dform subtype_df1 : except_mode[src] :: parens :: "prec"[prec_subtype] ::  ('A subtype 'B) =
   slot{'A} `" " sqsubseteq space slot{'B}

dform subtype_df2 : mode[src] :: parens :: "prec"[prec_subtype] :: ('A subtype 'B) =
   'A `" subtype " 'B

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rules

   @modsubsection{Typehood and equality}

   The << \subtype{'A; 'B} >> term is a type if both
   $A$ and $B$ are types.  The equality is @emph{intensional}:
   two subtype-types are equal if their subterms are equal.
   @end[doc]
>>
prim subtypeEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H> >- 'B1 = 'B2 in univ[i:l] } -->
   sequent { <H> >- 'A1 subtype 'B1 = 'A2 subtype 'B2 in univ[i:l] } =
   it

prim subtypeType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- "type"{'A subtype 'B} } =
   it

doc <:doc<
   @begin[doc]
   The intensional interpretation of typehood also means that if
   the subtype judgment <<'A subtype 'B>> is true, then both $A$
   and $B$ are types.
   @end[doc]
>>
prim subtypeTypeRight 'B :
   [main] sequent { <H> >- 'A subtype 'B } -->
   sequent { <H> >- "type"{'A} } =
   it

prim subtypeTypeLeft 'A :
   [main] sequent { <H> >- 'A subtype 'B }  -->
   sequent { <H> >- "type"{'B} } =
   it

interactive subtypeElimTypeRight {| nth_hyp |} 'H :
	sequent { <H>; w: 'A subtype 'B; <J['w]> >- 'A Type }

interactive subtypeElimTypeLeft  {| nth_hyp |} 'H :
	sequent { <H>; w: 'A subtype 'B; <J['w]> >- 'B Type }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction}

   The @tt[subtype_axiomFormation] rule gives the introduction form
   for the subtype judgment.  A type <<'A subtype 'B>> is true if $A$
   and $B$ are types, and any term $t @in A$ is also in $B$.  The
   proof extract term is always the $@it$ term.
   @end[doc]
>>
prim subtype_axiomFormation {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [main] sequent { <H>; x: 'A >- 'x in 'B } -->
   sequent { <H> >- 'A subtype 'B } =
   it

doc <:doc<
   @begin[doc]
   @modsubsection{Elimination}

   Subtype elimination has two forms.  The standard @tt[subtypeElimination]
   form corresponds to induction: the witness $x@colon <<'A subtype 'B>>$ is
   replaced with the unique proof term <<it>>.  The second rule
   @tt[use_subtypeT] postulates that <<'A subtype 'B>> with <<'a in 'A>>
   imply <<'a in 'B>>. Finally, @hrefrule[subtypeElimination2] reformulates
   @tt[use_subtypeT] in an elimination form.
   @end[doc]
>>
prim subtypeElimination {| elim [ThinOption thinT] |} 'H :
   ('t['x] : sequent { <H>; x: 'A subtype 'B; <J[it]> >- 'C[it] }) -->
   sequent { <H>; x: 'A subtype 'B; <J['x]> >- 'C['x] } =
   't[it]

prim useSubtype 'A :
   sequent { <H> >- 'A subtype 'B } -->
   sequent { <H> >- 'a = 'b in 'A } -->
   sequent { <H> >- 'a = 'b in 'B } =
   it

interactive subtypeElimination2 'H 'a 'b :
   [wf] sequent { <H>; x: 'A subtype 'B; <J['x]> >- 'a='b in 'A } -->
   sequent { <H>; x: 'A subtype 'B; <J['x]>; y:'a='b in 'B >- 'C['x] } -->
   sequent { <H>; x: 'A subtype 'B; <J['x]> >- 'C['x] }

doc <:doc<
   @begin[doc]
   @modsubsection{Member equality}
   The subtype-type, if true, contains only the term $@it$.
   For $@it$ to be in <<'A subtype 'B>>, the subtype judgment
   must be true.
   @end[doc]
>>
interactive subtype_axiomEquality {| intro []; squash |} :
   [main] sequent { <H> >- 'A subtype 'B } -->
   sequent { <H> >- it in 'A subtype 'B }

doc docoff

(************************************************************************
 * SUBTYPE RESOURCE                                                     *
 ************************************************************************)

type sub_info_type = (term * term) list * tactic

type sub_resource_info =
   LRSubtype of sub_info_type
 | RLSubtype of sub_info_type
 | DSubtype of sub_info_type

doc <:doc<
   @begin[doc]
   @resources

   The @tt{Itt_subtype} module defines the @resource[subtype_resource], which is
   used to prove subtyping judgments.  The @tt[sub_resource_info] argument
   requires two terms <<'t_1 subtype 't_2>> that match the goal term, and
   a tactic that can be used to refine goals of that form.
   @end[doc]
   @docoff
>>

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
                  (_, _, tac)::sg' -> tac::(aux sg' t)
                | [] -> raise (RefineError ("subtypeT", StringError "subtype mismatch"))
            else
               idT::(aux sg t)
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
         tac
   in
      funT subtyper

(*
 * Resource.
 *)
let resource (sub_resource_info, tactic) sub =
   Functional {
      fp_empty = empty_dtable;
      fp_add = improve_data;
      fp_retr = extract_data
   }

(*
 * Resource argument.
 *)
let prove_subtypeT = funT (fun p ->
   Sequent.get_resource_arg p get_sub_resource)

let resource intro +=
   subtype_term, ("prove_subtype",None,false,prove_subtypeT)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_subtypeT = argfunT (fun i p ->
   try
      let args = get_with_args p in
         match args with
           [a] -> subtypeElimination2 i a a |
           [a;b] -> subtypeElimination2 i a b |
           _ -> raise (RefineError ("subtypeElimination", StringError ("1 or 2 arguments required")))
   with RefineError ("get_attribute",_) -> subtypeElimination i)

let resource elim += (subtype_term, d_hyp_subtypeT)

interactive use_subtype1 'A :
   [aux] sequent { <H> >- 'A subtype 'B } -->
   [main] sequent { <H> >- 't1 = 't2 in 'A } -->
   sequent { <H> >- 't1 = 't2 in 'B }

interactive use_subtype2 'A :
   [aux] sequent { <H> >- 'A subtype 'B } -->
   [main] sequent { <H> >- 'A } -->
   sequent { <H> >- 'B }

let subtypeT = argfunT (fun t p ->
   if is_equal_term (Sequent.concl p) then
      use_subtype1 t
   else
      use_subtype2 t)

interactive by_subtype 'H:
   sequent { <H>; x:'A; <J['x]> >- 'A subtype 'B } -->
   sequent { <H>; x:'A; <J['x]> >- 'x in 'B }

let bySubtypeT = funT (fun p ->
   let b, x, _ = dest_equal (concl p) in
   let x = dest_var x in
   let xdecl = get_decl_number p x in
   let a = nth_hyp p xdecl in
   let t = <:con< "subtype"{$a$; $b$} >> in
   let subt = get_hyp_number p t in
      by_subtype xdecl thenT hypothesis subt)

let resource intro +=
   << !x in 'B >>, wrap_intro bySubtypeT

interactive subtypeReflexivity {| intro[] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'A subtype 'A }

interactive subtypeTransitive 'C :
   sequent { <H> >- 'A subtype 'C } -->
   sequent { <H> >- 'C subtype 'B } -->
   sequent { <H> >- 'A subtype 'B }

interactive subtypeTransitiveHyp1 'H :
	sequent { <H>; w: 'A subtype 'C; <J['w]> >- 'C subtype 'B } -->
	sequent { <H>; w: 'A subtype 'C; <J['w]> >- 'A subtype 'B }

interactive subtypeTransitiveHyp2 'H :
	sequent { <H>; w: 'C subtype 'B; <J['w]> >- 'A subtype 'C } -->
	sequent { <H>; w: 'C subtype 'B; <J['w]> >- 'A subtype 'B }

(*
 * H >- Ui ext subtype(A; B)
 * by subtypeFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
interactive subtypeFormation :
   sequent { <H> >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] }

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (subtype_term, infer_univ_dep0_dep0 dest_subtype)

(************************************************************************
 * TYPEHOOD FROM SUBTYPE                                                *
 ************************************************************************)

let type_subtype_leftT = subtypeTypeLeft
let type_subtype_rightT = subtypeTypeRight

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
