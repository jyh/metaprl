(*
 * Dependent functions.
 *
 *)

open Debug
open Term
open Options
open Refine_sig
open Resource

include Var

include Itt_equal
include Itt_rfun

(* debug_string DebugLoad "Loading itt_void..." *)

(*
 * H >- Ui ext a:A -> B
 * by functionFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
prim functionFormation 'H 'a 'A :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   ('B['a] : sequent ['ext] { 'H; a: 'A >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   a:'A -> 'B

(*
 * H >- (a1:A1 -> B1[a1]) = (a2:A2 -> B2[a2]) in Ui
 * by functionEquality x
 *
 * H >- A1 = A2 in Ui
 * H, x: A1 >- B1[x] = B2[x] in Ui
 *)
prim functionEquality 'H 'x :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[@i:l] } -->
   sequent ['ext] { 'H >- (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[@i:l] } =
   it

(*
 * H >- a:A -> B[a] ext lambda(z. b[z])
 * by lambdaFormation Ui z
 *
 * H >- A = A in Ui
 * H, z: A >- B[z] ext b[z]
 *)
prim lambdaFormation 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   ('b['z] : sequent ['ext] { 'H; z: 'A >- 'B['z] }) -->
   sequent ['ext] { 'H >- a:'A -> 'B['a] } =
   lambda{z. 'b['z]}

(*
 * H >- lambda(a1. b1[a1]) = lambda(a2. b2[a2]) in a:A -> B
 * by lambdaEquality Ui x
 *
 * H >- A = A in Ui
 * H, x: A >- b1[x] = b2[x] in B[x]
 *)
prim lambdaEquality 'H 'x :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'A >- 'b1['x] = 'b2['x] in 'B['x] } -->
   sequent ['ext] { 'H >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in a:'A -> 'B['a] } =
   it

(*
 * H >- f = g in x:A -> B
 * by functionExtensionality Ui (y:C -> D) (z:E -> F) u
 *
 * H, u:A >- f(u) = g(u) in B[u]
 * H >- A = A in Ui
 * H >- f = f in y:C -> D
 * H >- g = g in z:E -> F
 *)
prim functionExtensionality 'H (y:'C -> 'D['y]) (z:'E -> 'F['z]) 'u :
   sequent [squash] { 'H; u: 'A >- ('f 'u) = ('g 'u) in 'B['u] } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- 'f = 'f in y:'C -> 'D['y] } -->
   sequent [squash] { 'H >- 'g = 'g in z:'E -> 'F['z] } -->
   sequent ['ext] { 'H >- 'f = 'g in x:'A -> 'B['x] } =
   it

(*
 * H, f: (x:A -> B), J[x] >- T[x] t[f, f a, it]
 * by functionElimination i a y v
 *
 * H, f: (x:A -> B), J[x] >- a = a in A
 * H, f: (x:A -> B), J[x], y: B[a], v: y = f(a) in B[a] >- T[x] ext t[f, y, v]
 *)
prim functionElimination 'H 'J 'f 'a 'y 'v :
   sequent [squash] { 'H; f: x:'A -> 'B; 'J['f] >- 'a = 'a in 'A } -->
   ('t['f; 'y; 'v] : sequent ['ext] { 'H; f: x:'A -> 'B; 'J['f]; y: 'B['a]; v: 'y = ('f 'a) in 'B['a] >- 'T['f] }) -->
   sequent ['ext] { 'H; f: x:'A -> 'B; 'J['f] >- 'T['f] } =
   't['f; 'f 'a; it]

(*
 * H >- (f1 a1) = (f2 a2) in B[a1]
 * by applyEquality (x:A -> B[x])
 *
 * H >- f1 = f2 in x:A -> B[x]
 * H >- a1 = a2 in A
 *)
prim applyEquality 'H (x:'A -> 'B['x]) :
   sequent [squash] { 'H >- 'f1 = 'f2 in x:'A -> 'B['x] } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- ('f1 'a1) = ('f2 'a2) in 'B['a1] } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Template.
 *)
let dfun_term = << x: 'A -> 'B['x] >>

(*
 * Primitives.
 *)
let dfun_opname = opname_of_term dfun_term
let is_dfun_term = is_dep0_dep1_term dfun_opname
let dest_dfun = dest_dep0_dep1_term dfun_opname
let mk_dfun_term = mk_dep0_dep1_term dfun_opname

(*
 * D the conclusion.
 *)
let d_concl_dfun p =
   let count = hyp_count p in
   let t = concl p in
   let z, _, _ = dest_dfun t in
   let z' = get_opt_var_arg z p in
      lambdaFormation count z' p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_dfun i p =
   let a =
      try get_term_arg 0 p with
         Not_found ->
            raise (RefineError (StringError "d_hyp_dfun: requires an argument"))
   in
   let count = hyp_count p in
   let i' = get_pos_hyp_index i count in
   let f = var_of_hyp i' p in
      (match maybe_new_vars ["y"; "v"] (declared_vars p) with
          [y; v] ->
             functionElimination i' (count - i' - 1) f a y v
             thenLT [addHiddenLabelT "wf"; idT]
        | _ ->
             failT) p

(*
 * Join them.
 *)
let d_dfun i =
   if i = 0 then
      d_concl_dfun
   else
      d_hyp_dfun i

let d_resource = d_resource.resource_improve d_resource (dfun_term, d_dfun)
let d = d_resource.resource_extract d_resource

(*
 * EQCD.
 *
 * Need a term for the well-order.
 *)
let eqcd_dfun p =
   let x = get_opt_var_arg "x" p in
   let count = hyp_count p in
      (functionEquality count x
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (dfun_term, eqcd_dfun)
let eqcd = eqcd_resource.resource_extract eqcd_resource

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:52:08  jyh
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
 * Revision 1.4  1996/10/23 15:18:05  jyh
 * First working version of dT tactic.
 *
 * Revision 1.3  1996/05/21 02:16:36  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:33:51  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/28 02:51:27  jyh
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
