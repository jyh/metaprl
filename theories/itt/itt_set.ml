(*
 * Set type.
 *
 *)

include Itt_squash
include Itt_equal
include Itt_unit
include Itt_subtype
include Itt_struct

open Printf
open Debug
open Options
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineErrors
open Resource

open Tacticals
open Var
open Itt_squash
open Itt_struct
open Itt_equal
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_set%t" eflush

(* debug_string DebugLoad "Loading itt_set..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare set{'A; x. 'B['x]}
declare hide{'A}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform set_df1 : set{'A; x. 'B['x]} = "{" bvar{'x} `":" 'A `"|" 'B['x] "}"
dform hide_df1 : mode[prl] :: hide{'A} = "[" 'A "]"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext { a:A | B }
 * by setFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
prim setFormation 'H 'a 'A :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] }
   ('B['a] : sequent ['ext] { 'H; a: 'A >- univ[@i:l] }) :
   sequent ['ext] { 'H >- univ[@i:l] } =
   { a: 'A | 'B['a] }

(*
 * H >- { a1:A1 | B1[a1] } = { a2:A2 | B2[a2] } in Ui
 * by setEquality x
 *
 * H >- A1 = A2 in Ui
 * H, x: A1 >- B1[x] = B2[x] in Ui
 *)
prim setEquality 'H 'x :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] }
   sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[@i:l] } :
   sequent ['ext] { 'H >- { a1:'A1 | 'B1['a1] } = { a2:'A2 | 'B2['a2] } in univ[@i:l] } = it

(*
 * H >- { a:A | B[a] } ext a
 * by setMemberFormation Ui a z
 *
 * H >- a = a in A
 * H >- B[a]
 * H, z: A >- B[z] = B[z] in Ui
 *)
prim setMemberFormation 'H 'a 'z :
   sequent [squash] { 'H >- 'a = 'a in 'A }
   sequent ['ext]   { 'H >- 'B['a] }
   sequent [squash] { 'H; z: 'A >- "type"{'B['z]} } :
   sequent ['ext]   { 'H >- { x:'A | 'B['x] } } =
   'a

(*
 * H >- a1 = a2 in { a:A | B }
 * by setMemberEquality Ui x
 *
 * H >- a1 = a2 in A
 * H >- B[a1]
 * H, x: A >- B[x] = B[x] in Ui
 *)
prim setMemberEquality 'H 'x :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A }
   sequent [squash] { 'H >- 'B['a1] }
   sequent [squash] { 'H; x: 'A >- "type"{'B['x]} } :
   sequent ['ext] { 'H >- 'a1 = 'a2 in { a:'A | 'B['a] } } = it

(*
 * H, u: { x:A | B }, J[u] >- T[u] ext t[y]
 * by setElimination y v
 *
 * H, u: { x:A | B }, y: A; v: hide(B[y]); J[y] >- T[y]
 *)
prim setElimination 'H 'J 'u 'y 'v :
   sequent [squash] { 'H; u: { x:'A | 'B['x] }; y: 'A; v: 'B['y]; 'J['y] >- 'T['y] } :
   sequent [squash] { 'H; u: { x:'A | 'B['x] }; 'J['u] >- 'T['u] } =
   it

(*
 * H, u: { x:A | B }, J[u] >> T[u] ext t[y]
 * by setElimination2 y v z
 * H, u: { x:A | B }, y: A; v: hide(B[y]); J[y] >> T[y]
 *)
prim setElimination2 'H 'J 'u 'y 'v :
   ('t['u; 'y; 'v] : sequent [it; 'prop] { 'H; u: { x:'A | 'B['x] }; y: 'A; v: hide{'B['y]}; 'J['y] >- 'T['y] }) -->
   sequent [it; 'prop] { 'H; u: { x:'A | 'B['x] }; 'J['u] >- 'T['u] } =
   't['u; 'u; it]

(*
 * Unhiding.
 *)
prim hideElimination 'H 'J :
   sequent [squash] { 'H; u: 'P; 'J[it] >- 'T[it] } -->
   sequent [squash] { 'H; u: hide{'P}; 'J['u] >- 'T['u] } =
   it

(*
 * Subtyping.
 *)
prim set_subtype 'H :
   sequent [squash] { 'H >- "type"{ { a: 'A | 'B['a] } } } -->
   sequent ['ext] { 'H >- subtype{ { a: 'A | 'B['a] }; 'A } } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let set_term = << { a: 'A | 'B['x] } >>

(*
 * D
 *)
let d_set i p =
   if i = 0 then
      let t =
         try get_with_arg p with
            Not_found ->
               raise (RefineError ("d_set", StringError "requires an argument"))
      in
      let v = get_opt_var_arg "z" p in
         setMemberFormation (Sequent.hyp_count p) t v p
   else
      let i, j = Sequent.hyp_indices p i in
      let n, _ = Sequent.nth_hyp p i in
         match maybe_new_vars ["y"; "v"] (Sequent.declared_vars p) with
            [u; y; v] ->
               setElimination i j u y v p
          | _ ->
               failwith "d_set: match"

let d_resource = d_resource.resource_improve d_resource (set_term, d_set)
let d = d_resource.resource_extract d_resource

(*
 * EqCD.
 *)
let eqcd_set p =
   let count = Sequent.hyp_count p in
   let v = get_opt_var_arg "x" p in
      setEquality count v p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (set_term, eqcd_set)
let eqcd = eqcd_resource.resource_extract eqcd_resource

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let set_term = << { a: 'A | 'B['a] } >>
let set_opname = opname_of_term set_term
let is_set_term = is_dep0_dep1_term set_opname
let dest_set = dest_dep0_dep1_term set_opname
let mk_set_term = mk_dep0_dep1_term set_opname

let hide_term = << hide{'a} >>
let hide_opname = opname_of_term hide_term
let is_hide_term = is_dep0_term hide_opname
let dest_hide = dest_dep0_term hide_opname
let mk_hide_term = mk_dep0_term hide_opname

(*
 * Squash a goal.
 *)
let squashT p =
   (if is_squash_goal p then
       idT
    else
       squash_of_proof p) p

(*
 * Unhide a hidden hypothesis.
 *)
let unhideT i p =
   let i, j = Sequent.hyp_indices p i in
   let s = dest_hide (snd (Sequent.nth_hyp p i)) in
      (assertAtT (i + 1) s
       thenLT [squashT thenMT nthHypT i;
               thinT i]) p

(*
 * Unhide all hidden hyps.
 *)
let unhideAllT p =
   let count = Sequent.hyp_count p in
   let rec aux i p =
      (if i < count then
          let _, h = Sequent.nth_hyp p i in
             if is_hide_term h then
                unhideT i thenMT aux (i + 1)
             else
                aux (i + 1)
       else
          idT) p
   in
      aux 0 p

(*
 * D
 *)
let d_set_concl p =
   let t =
      try get_with_arg p with
         Not_found ->
            raise (RefineError ("d_set", StringError "requires an argument"))
   in
   let v = get_opt_var_arg "z" p in
      setMemberFormation (Sequent.hyp_count p) t v p

let d_set_hyp i p =
   let i, j = Sequent.hyp_indices p i in
   let n, _ = Sequent.nth_hyp p i in
   let d_squashed p =
      (match maybe_new_vars ["y"; "v"] (Sequent.declared_vars p) with
          [y; v] ->
             setElimination i j n y v
        | _ ->
             failT) p
   in
   let d_hidden p =
      (match maybe_new_vars ["y"; "v"] (Sequent.declared_vars p) with
          [y; v] ->
             setElimination2 i j n y v
        | _ -> 
             failT) p
   in
      (if is_squash_goal p then
          d_squashed
       else
          let squash = squash_of_proof p in
          let tac =
             d_hidden thenT tryT (unhideT (i + 2))
          in
             (squash thenMT d_squashed) orelseT tac) p

let d_setT i =
   if i = 0 then
      d_set_concl
   else
      d_set_hyp i

let d_resource = d_resource.resource_improve d_resource (set_term, d_setT)

(*
 * EqCD.
 *)
let eqcd_setT p =
   let count = Sequent.hyp_count p in
   let v = get_opt_var_arg "x" p in
      setEquality count v p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (set_term, eqcd_setT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of atom.
 *)
let inf_set f decl t =
   let v, ty, prop = dest_set t in
   let decl', ty' = f decl ty in
   let decl'', prop' = f ((v, ty)::decl') prop in
   let le1, le2 =
      try dest_univ ty', dest_univ prop' with
         Term.TermMatch _ -> raise (RefineError ("typeinf", StringTermError ("can't infer type for", t)))
   in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (set_term, inf_set)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

let set_subtypeT p =
   (set_subtype (Sequent.hyp_count p)
    thenT addHiddenLabelT "wf") p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (LRSubtype ([<< { a: 'A | 'B['a] } >>, << 'A >>], set_subtypeT))

(*
 * $Log$
 * Revision 1.9  1998/07/01 04:37:48  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.8  1998/06/12 13:47:37  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.7  1998/06/09 20:52:43  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.6  1998/06/01 13:56:15  jyh
 * Proving twice one is two.
 *
 * Revision 1.5  1998/05/28 13:48:01  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.4  1998/04/24 02:43:45  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.3  1998/04/22 22:45:08  jyh
 * *** empty log message ***
 *
 * Revision 1.2  1997/08/06 16:18:41  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:25  jyh
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
 * Revision 1.3  1996/05/21 02:17:09  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:14  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/30 01:37:18  jyh
 * Initial version of ITT.
 *
 * Revision 1.2  1996/03/28 02:51:28  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.1  1996/03/05 19:59:41  jyh
 * Version just before LogicalFramework.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
