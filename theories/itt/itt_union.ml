(*
 * Rules for dependent product.
 *
 *)

open Debug
open Options
open Refine_sig
open Resource

include Var

include Itt_equal
include Itt_rfun

(* debug_string DebugLoad "Loading itt_union..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare union{'A; 'B}
declare inl{'x}
declare inr{'x}
declare decide{'x; y. 'a['y]; z. 'b['z]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Reduction on decide.
 * decide(inl x; u. l[u]; v. r[v]) <--> l[x]
 * decide(inr x; u. l[u]; v. r[v]) <--> r[x]
 *)
primrw inlReduce : decide{inl{'x}; u. 'l['u]; v. 'r['v]} <--> 'l['x]
primrw inrReduce : decide{inr{'x}; u. 'l['u]; v. 'r['v]} <--> 'r['x]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext A + B
 * by unionFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
prim unionFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[@i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   'A + 'B

(*
 * H >- A1 + B1 = A2 + B2 in Ui
 * by unionEquality
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
prim unionEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- 'A1 + 'B1 = 'A2 + 'B2 in univ[@i:l] } =
   it

(*
 * H >- A + B ext inl a
 * by inlFormation
 * H >- A
 * H >- B = B in Ui
 *)
prim inlFormation 'H :
   ('a : sequent ['ext] { 'H >- 'A }) -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- 'A + 'B } =
   inl{'a}

(*
 * H >- A + B ext inl a
 * by inrFormation
 * H >- B
 * H >- A = A in Ui
 *)
prim inrFormation 'H :
   ('b : sequent ['ext] { 'H >- 'B }) -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- 'A + 'B } =
   inr{'b}

(*
 * H >- inl a1 = inl a2 in A + B
 * by inlEquality
 * H >- a1 = a2 in A
 * H >- B = B in Ui
 *)
prim inlEquality 'H :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- inl{'a1} = inl{'a2} in 'A + 'B } =
   it

(*
 * H >- inr b1 = inr b2 in A + B
 * by inrEquality
 * H >- b1 = b2 in B
 * H >- A = A in Ui
 *)
prim inrEquality 'H :
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- inr{'b1} = inr{'b2} in 'A + 'B } =
   it

(*
 * H, x: A + B, J[x] >- T[x] ext decide(x; u. 'left['u]; v. 'right['v])
 * by unionElimination x u v
 * H, x: A # B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
prim unionElimination 'H 'J 'x 'u 'v :
   ('left['u] : sequent ['ext] { 'H; x: 'A + 'B; u: 'A; 'J[inl('u)] >- 'T[inl('u)] }) -->
   ('right['u] : sequent ['ext] { 'H; x: 'A + 'B; v: 'B; 'J[inr('v)] >- 'T[inr('v)] }) -->
   sequent ['ext] { 'H; x: 'A + 'B; 'J['x] >- 'T['x] } =
   decide{'x; u. 'left['u]; v. 'right['v]}

(*
 * H >- decide(e1; u1. l1[u1]; v1. r1[v1]) = decide(e2; u2. l2[u2]; v2. r2[v2]) in T[e1]
 * by unionEquality lambda(z. T[z]) (A + B) u v w
 * H >- e1 = e2 in A + B
 * H, u:A, w: e1 = inl u in A + B >- l1[u] = l2[u] in T[inl{u}]
 * H, v:A, w: e1 = inr v in A + B >- r1[v] = r2[v] in T[inr{v}]
 *)
prim decideEquality 'H lambda{z. 'T['z]} ('A + 'B) 'u 'v 'w :
   sequent [squash] { 'H >- 'e1 = 'e2 in 'A + 'B } -->
   sequent [squash] { 'H; u: 'A; w: 'e1 = inl{'u} in 'A + 'B >- 'l1['u] = 'l2['u] in 'T[inl{'u}] } -->
   sequent [squash] { 'H; v: 'B; w: 'e1 = inr{'v} in 'A + 'B >- 'r1['v] = 'r2['v] in 'T[inr{'v}] } -->
   sequent ['ext] { 'H >- decide{'e1; u1. 'l1['u1]; v1. 'r1['v1]} =
                   decide{'e2; u2. 'l2['u2]; v2. 'r2['v2]} in
                   'T['e1] } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_union p =
   let count = hyp_count p in
   let flag =
      try get_int_arg 0 p with
         Not_found -> raise (RefineError (StringError "d_concl_union: requires a flag"))
   in
   let tac =
      match flag with
         1 -> inlFormation
       | 2 -> inrFormation
       | _ -> raise (RefineError (StringError "d_concl_union: select either 1 or 2"))
   in
      (tac count thenLT [idT; addHiddenLabelT "wf"]) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_union i p =
   let count = hyp_count p in
   let i' = get_pos_hyp_index i count in
   let z = var_of_hyp i' p in
      (match maybe_new_vars [z; z] (declared_vars p) with
          [u; v] ->
             unionElimination i' (count - i' - 1) z u v
        | _ ->
             failT) p

(*
 * Join them.
 *)
let d_union i =
   if i = 0 then
      d_concl_union
   else
      d_hyp_union i

let union_term = << 'A + 'B >>

let d_resource = d_resource.resource_improve d_resource (union_term, d_union)
let d = d_resource.resource_extract d_resource

(*
 * EQCD.
 *)
let eqcd_union p =
   let count = hyp_count p in
      (unionEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (union_term, eqcd_union)
let eqcd = eqcd_resource.resource_extract eqcd_resource

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:52:30  jyh
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
 * Revision 1.3  1996/10/23 15:18:13  jyh
 * First working version of dT tactic.
 *
 * Revision 1.2  1996/05/21 02:17:27  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.1  1996/03/28 02:51:35  jyh
 * This is an initial version of the type theory.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
