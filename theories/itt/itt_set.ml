(*
 * Set type.
 *
 *)

open Debug
open Options
open Term
open Refine_sig
open Resource

include Var

include Itt_equal

(* debug_string DebugLoad "Loading itt_set..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare set{'A; x. 'B['x]}
declare hide{'A}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform set{'A; x. 'B['x]} = "{" bvar{'x} `":" 'A `"|" 'B['x] "}"
dform mode[prl] :: hide{'A} = "[" 'A "]"

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
   ('t['u; 'y; 'v] : sequent ['ext] { 'H; u: { x:'A | 'B['x] }; y: 'A; v: hide{'B['y]}; 'J['y] >- 'T['y] }) :
   sequent ['ext] { 'H; u: { x:'A | 'B['x] }; 'J['u] >- 'T['u] } =
   't['u; 'u; it]

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
         try get_term_arg 1 p with
            Not_found ->
               raise (RefineError (StringError "d_set requires an argument"))
      in
      let v = get_opt_var_arg "z" p in
         setMemberFormation (hyp_count p) t v p
   else
      let count = hyp_count p in
      let i' = get_pos_hyp_index i count in
      let n = var_of_hyp i' p in
         match maybe_new_vars ["y"; "v"] (Sequent.declared_vars p) with
            [u; y; v] ->
               setElimination i' (count - i' - 1) u y v p
          | _ ->
               failwith "d_set: match"
         
let d_resource = d_resource.resource_improve d_resource (set_term, d_set)
let d = d_resource.resource_extract d_resource

(*
 * EqCD.
 *)
let eqcd_set p =
   let count = hyp_count p in
   let v = get_opt_var_arg "x" p in
      setEquality count v p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (set_term, eqcd_set)
let eqcd = eqcd_resource.resource_extract eqcd_resource

(*
 * $Log$
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
