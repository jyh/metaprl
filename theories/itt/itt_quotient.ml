(*
 * Quotient type.
 *
 *)

include Tacticals

include Itt_equal
include Itt_set
include Itt_rfun

open Printf
open Debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Resource

open Var
open Sequent
open Tacticals

open Itt_equal
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_quotient%t" eflush

(* debug_string DebugLoad "Loading itt_quotient..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "quot"{'A; x, y. 'E['x; 'y]}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_quot

dform quot_df1 : mode[prl] :: parens :: "prec"[prec_quot] :: "quot"{'A; x, y. 'E['x; 'y]} =
   slot{'x} `"," slot{'y} `":" slot{'A} `"//" slot{'E['x; 'y]}

dform quot_df2 : mode[src] :: parens :: "prec"[prec_quot] :: "quot"{'A; x, y. 'E['x; 'y]} =
   `"quot " slot{'x} `", " slot{'y} `":" slot{'A} `"//" slot{'E['x; 'y]}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext quot x, y: A // E
 * by quotientFormation (quot x, y: A // E) z u v
 *
 * H >- A = A in Ui
 * H, x: A, y: A >- E[x, y] = E[x, y] in Ui
 * H, x: A >- E[x, x]
 * H, x: A, y: A, u: E[x, y] >- E[y, x]
 * H, x: A, y: A, z: A, u: E[x, y], v: E[y, z] >- E[x, z]
 *)
prim quotientFormation 'H (quot x, y: 'A // 'E['x; 'y]) 'z 'u 'v :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A; y: 'A >- 'E['x; 'y] = 'E['x; 'y] in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A >- 'E['x; 'x] } -->
   sequent [squash] { 'H; x: 'A; y: 'A; u: 'E['x; 'y] >- 'E['y; 'x] } -->
   sequent [squash] { 'H; x: 'A; y: 'A; z: 'A; u: 'E['x; 'y]; v: 'E['y; 'z] >- 'E['x; 'z] } -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   quot x, y: 'A // 'E['x; 'y]

(*
 * H >- quot x1, y1: A1 // E1 = quot x2, y2. A2 // E2 in Ui
 * by quotientWeakEquality x y z u v
 *
 * H >- A1 = A2 in Ui
 * H, x: A1, y: A1 >- E1[x, y] = E2[x, y] in Ui
 * H, x: A1 >- E1[x, x]
 * H, x: A1, y: A1, u: E1[x, y] >- E1[y, x]
 * H, x: A1, y: A1, z: A1, u: E1[x, y], v: E1[y, z] >- E1[x, z]
 *)
prim quotientWeakEquality 'H 'x 'y 'z 'u 'v :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A1; y: 'A1 >- 'E1['x; 'y] = 'E2['x; 'y] in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A1 >- 'E1['x; 'x] } -->
   sequent [squash] { 'H; x: 'A1; y: 'A1; u: 'E1['x; 'y] >- 'E1['y; 'x] } -->
   sequent [squash] { 'H; x: 'A1; y: 'A1; z: 'A1; u: 'E1['x; 'y]; v: 'E1['y; 'z] >- 'E1['x; 'z] } -->
   sequent ['ext] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1]
                   = quot x2, y2: 'A2 // 'E2['x2; 'y2]
                   in univ[@i:l]
           } =
   it

(*
 * H >- quot x1, y1: A1 // E1 = quot x2, y2. A2 // E2 in Ui
 * by quotientEquality r s v
 *
 * H >- quot x1, y1: A1 // E1 = quot x1, y1: A1 // E1 in Ui
 * H >- quot x2, y2. A2 // E2 = quot x2, y2. A2 // E2 in Ui
 * H >- A1 = A2 in Ui
 * H; v: A1 = A2 in Ui; r: A1; s: A1 >- E1[r, s] -> E2[r, s]
 * H; v: A1 = A2 in Ui; r: A1; s: A1 >- E2[r, s] -> E1[r, s]
 *)
prim quotientEquality 'H 'r 's 'v :
   sequent [squash] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1] = quot x1, y1: 'A1 // 'E1['x1; 'y1] in univ[@i:l] } -->
   sequent [squash] { 'H >- quot x2, y2: 'A2 // 'E2['x2; 'y2] = quot x2, y2: 'A2 // 'E2['x2; 'y2] in univ[@i:l] } -->
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; v: 'A1 = 'A2 in univ[@i:l]; r: 'A1; s: 'A1 >- 'E1['r; 's] -> 'E2['r; 's] } -->
   sequent [squash] { 'H; v: 'A1 = 'A2 in univ[@i:l]; r: 'A1; s: 'A1 >- 'E2['r; 's] -> 'E1['r; 's] } -->
   sequent ['ext] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1] = quot x2, y2: 'A2 // 'E2['x2; 'y2] in univ[@i:l] } =
   it

(*
 * H >- quot x, y: A // E ext a
 * by quotient_memberFormation
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- A ext a
 *)
prim quotient_memberFormation 'H :
   sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   ('a : sequent ['ext] { 'H >- 'A }) -->
   sequent ['ext] { 'H >- quot x, y: 'A // 'E['x; 'y] } =
   'a

(*
 * H >- a1 = a2 in quot x, y: A // E
 * by quotient_memberWeakEquality
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- x1 = a2 in A
 *)
prim quotient_memberWeakEquality 'H :
   sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] } =
   it

(*
 * H >- a1 = a2 in quot x, y: A // E
 * by quotient_memberEquality
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- a1 = a1 in A
 * H >- a2 = a2 in A
 * H >- E[a1; a2]
 *)
prim quotient_memberEquality 'H :
   sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   sequent [squash] { 'H >- 'a1 = 'a1 in 'A } -->
   sequent [squash] { 'H >- 'a2 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'E['a1; 'a2] } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] } =
   it

(*
 * !!!!CHECK!!!!
 *
 * H, a: quot x, y: A // E, J[x] >- s[a] = t[a] in T[a]
 * by quotientElimination v w z
 *
 * H, a: quot x, y: A // E, J[x] >- T[a] = T[a] in Ui
 * H, a: quot x, y: A // E, J[x], v: A, w: A, z: E[v, w] >- s[v] = t[w] in T[v]
 *)
prim quotientElimination 'H 'J 'v 'w 'z :
   sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- "type"{'T['a]} } -->
   sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a];
             v: 'A; w: 'A; z: 'E['v; 'w] >- 's['v] = 't['w] in 'T['v]
           } -->
   sequent ['ext] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- 's['a] = 't['a] in 'T['a] } =
   it

(*
 * !!!!CHECK!!!!
 *
 * H, x: a1 = a2 in quot x, y: A // E, J[x] >- T[x]
 * by quotient_equalityElimination v
 *
 * H, x: a1 = a2 in quot x, y: A // E, J[x], v: hide(E[a, b]) >- T[x]
 *)
prim quotient_equalityElimination 'H 'J 'v :
   ('g['v] : sequent ['ext] { 'H; x: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; 'J['x]; v: hide('E['a1; 'a2]) >- 'T['x] }) -->
   sequent ['ext] { 'H; x: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; 'J['x] >- 'T['x] } =
   'g[it]

(*
 * H >- quot x1, y1: A1 // E1[x1; y1] <= quot x2, y2: A2 // E2[x2; y2]
 * by quotientSubtype
 *
 * H >- A1 <= A2
 * H, x1: A1, y1: A1 >- E1[x1; y1] => E2[x2; y2]
 * H >- quot x1, y1: A1 // E1[x1; y1] in type
 * H >- quot x2, y2: A2 // E2[x2; y2] in type
 *)
prim quotientSubtype 'H 'a1 'a2 :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H; a1: 'A1; a2: 'A1 (* ; 'E1['a1; 'a2] *) >- 'E2['a1; 'a2] } -->
   sequent [squash] { 'H >- "type"{(quot x1, y1: 'A1 // 'E1['x1; 'y1])} } -->
   sequent [squash] { 'H >- "type"{(quot x2, y2: 'A2 // 'E2['x2; 'y2])} } -->
   sequent ['ext] { 'H >- subtype{ (quot x1, y1: 'A1 // 'E1['x1; 'y1]); (quot x2, y2: 'A2 // 'E2['x2; 'y2]) } } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let quotient_term = << "quot"{'A; x, y. 'E['x; 'y]} >>
let quotient_opname = opname_of_term quotient_term
let is_quotient_term = is_dep0_dep2_term quotient_opname
let dest_quotient = dest_dep0_dep2_term quotient_opname
let mk_quotient_term = mk_dep0_dep2_term quotient_opname

(*
 * D the conclusion.
 *)
let d_concl_quotient p =
   let count = hyp_count p in
      quotient_memberFormation count p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_quotient i p =
   let i, j = hyp_indices p i in
      (match maybe_new_vars ["v"; "w"; "z"] (declared_vars p) with
          [v; w; z] ->
             quotientElimination i j v w z
        | _ ->
             failT) p

(*
 * Join them.
 *)
let d_quotientT i =
   if i = 0 then
      d_concl_quotient
   else
      d_hyp_quotient i

let d_resource = d_resource.resource_improve d_resource (quotient_term, d_quotientT)

(*
 * EQCD.
 *)
let eqcd_quotientT p =
   let count = hyp_count p in
      (match maybe_new_vars ["r"; "s"; "t"] (declared_vars p) with
          [r; s; t] ->
             quotientEquality count r s t
             thenT addHiddenLabelT "wf"
        | _ -> failT) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (quotient_term, eqcd_quotientT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of quotient.
 *)
let inf_quotient f decl t =
   let x, y, a, e = dest_quotient t in
   let decl', a' = f decl a in
   let decl'', e' = f ((x, a)::(y, a)::decl') e in
   let le1, le2 = dest_univ a', dest_univ e' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (quotient_term, inf_quotient)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two quotient types.
 *)
let quotient_subtypeT p =
   (match maybe_new_vars ["x"; "y"] (declared_vars p) with
       [x; y] ->
          (quotientSubtype (hyp_count p) x y
           thenLT [addHiddenLabelT "subtype";
                   addHiddenLabelT "aux";
                   addHiddenLabelT "wf";
                   addHiddenLabelT "wf"])

     | _ -> failT) p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (DSubtype ([<< quot x1, y1: 'A1 // 'E1['x1; 'y1] >>, << quot x2, y2: 'A2 // 'E2['x2; 'y2] >>;
               << 'A1 >>, << 'A2 >>],
              quotient_subtypeT))

(*
 * $Log$
 * Revision 1.12  1998/07/02 18:37:44  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.11  1998/07/01 04:37:45  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.10  1998/06/22 19:46:21  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.9  1998/06/12 13:47:35  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.8  1998/06/09 20:52:41  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.7  1998/06/01 13:56:09  jyh
 * Proving twice one is two.
 *
 * Revision 1.6  1998/05/28 13:47:54  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.5  1998/04/24 02:43:40  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.4  1998/04/22 22:45:03  jyh
 * *** empty log message ***
 *
 * Revision 1.3  1998/04/09 18:26:08  jyh
 * Working compiler once again.
 *
 * Revision 1.2  1997/08/06 16:18:37  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:22  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.4  1996/10/23 15:18:11  jyh
 * First working version of dT tactic.
 *
 * Revision 1.3  1996/05/21 02:17:03  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:10  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/30 01:37:16  jyh
 * Initial version of ITT.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
