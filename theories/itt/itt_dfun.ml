(*
 * Dependent functions.
 *
 *)

include Var

include Itt_equal
include Itt_rfun

open Printf
open Debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Resource

open Var
open Sequent
open Tacticals
open Itt_equal
open Itt_subtype
open Itt_rfun

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_dfun%t" eflush

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
   sequent [squash] { 'H; f: x:'A -> 'B['x]; 'J['f] >- 'a = 'a in 'A } -->
   ('t['f; 'y; 'v] : sequent ['ext] { 'H; f: x:'A -> 'B['x]; 'J['f]; y: 'B['a]; v: 'y = ('f 'a) in 'B['a] >- 'T['f] }) -->
   sequent ['ext] { 'H; f: x:'A -> 'B['x]; 'J['f] >- 'T['f] } =
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

(*
 * H >- a1:A1 -> B1 <= a2:A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H, a: A1 >- B1[a] <= B2[a]
 *)
prim functionSubtype 'H 'a :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['prop] { 'H >- subtype{ (a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2]) } } =
   it

(*
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; J[x] >- T[x]
 * by function_subtypeElimination i
 *
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; y: A2 <= A1; z: a:A2 -> B2[a] <= B1[a]; J[x] >- T[x]
 *)
prim function_subtypeElimination 'H 'J 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent { 'H;
             x: subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])};
             'J['x];
             y: subtype{'A2; 'A1};
             z: a:'A2 -> subtype{'B1['a]; 'B2['a]}
             >- 'T['x]
           }) -->
   sequent { 'H; x: subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])}; 'J['x] >- 'T['x] } =
   't['x; it; lambda{x. it}]

(*
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; J[x] >- T[x]
 * by function_equalityElimination
 *
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; y: A1 = A2 in Ui; z: a:A1 -> B1[a] = B2[a] in Ui; J[x] >- T[x]
 *)
prim function_equalityElimination 'H 'J 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent { 'H;
             x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[@i:l];
             'J['x];
             y: 'A1 = 'A2 in univ[@i:l];
             z: a:'A1 -> ('B1['a] = 'B2['a] in univ[@i:l])
             >- 'T['x]
           }) -->
   sequent { 'H; x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[@i:l]; 'J['x] >- 'T['x] } =
   't['x; it; lambda{x. it}]

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

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
      try get_with_arg p with
         Not_found ->
            raise (RefineError ("d_hyp_dfun", StringError "requires an argument"))
   in
   let count = hyp_count p in
   let f, _ = Sequent.nth_hyp p i in
   let i, j = hyp_indices p i in
      (match maybe_new_vars ["y"; "v"] (declared_vars p) with
          [y; v] ->
             functionElimination i j f a y v
             thenLT [addHiddenLabelT "wf"; idT]
        | _ ->
             failT) p

(*
 * Join them.
 *)
let d_dfunT i =
   if i = 0 then
      d_concl_dfun
   else
      d_hyp_dfun i

let d_resource = d_resource.resource_improve d_resource (dfun_term, d_dfunT)

(************************************************************************
 * EQCD TACTICS                                                         *
 ************************************************************************)

(*
 * EQCD dfun.
 *)
let eqcd_dfunT p =
   let _, x, _ = dest_equal (concl p) in
   let v, _, _ = dest_dfun x in
   let x = get_opt_var_arg v p in
   let count = hyp_count p in
      (functionEquality count x
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (dfun_term, eqcd_dfunT)

(*
 * EQCD lambda.
 *)
let eqcd_lambdaT p =
   let _, l, _ = dest_equal (concl p) in
   let v, _ = dest_lambda l in
   let x = get_opt_var_arg v p in
   let count = hyp_count p in
      (lambdaEquality count x
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (lambda_term, eqcd_lambdaT)

(*
 * EQCD apply.
 *)
let eqcd_applyT p =
   let t =
      try get_with_arg p with
         Not_found -> raise (RefineError ("eqcd_applyT", StringError "need an argument"))
   in
   let count = hyp_count p in
      (applyEquality count t
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (apply_term, eqcd_applyT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_dfun f decl t =
   let v, a, b = dest_dfun t in
   let decl', a' = f decl a in
   let decl'', b' = f ((v, a)::decl') b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (dfun_term, inf_dfun)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let dfun_subtypeT p =
   let a = get_opt_var_arg "x" p in
      (functionSubtype (hyp_count p) a
       thenT addHiddenLabelT "subtype") p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (DSubtype ([<< a1:'A1 -> 'B1['a1] >>, << a2:'A2 -> 'B2['a2] >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              dfun_subtypeT))

(*
 * $Log$
 * Revision 1.12  1998/07/02 18:37:25  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.11  1998/07/01 04:37:35  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.10  1998/06/23 22:12:28  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 * Revision 1.9  1998/06/12 13:47:23  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.8  1998/06/09 20:52:31  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.7  1998/06/01 13:55:47  jyh
 * Proving twice one is two.
 *
 * Revision 1.6  1998/05/28 13:47:25  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.5  1998/04/24 02:43:23  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.4  1998/04/22 22:44:37  jyh
 * *** empty log message ***
 *
 * Revision 1.3  1997/08/07 19:43:51  jyh
 * Updated and added Lori's term modifications.
 * Need to update all pattern matchings.
 *
 * Revision 1.2  1997/08/06 16:18:24  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
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
