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

(* debug_string DebugLoad "Loading itt_dprod..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(* declare prod{'A; 'B} *)
declare prod{'A; x. 'B['x]}
declare pair{'a; 'b}
declare spread{'e; u, v. 'b['u; 'v]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Reduction on spread:
 * spread(u, v; a, b. c[a, b]) <--> c[u, v]
 *)
primrw spreadReduce : spread{'u, 'v; a, b. 'c['a; 'b]} <--> 'c['u; 'v]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prod
prec spread

dform parens :: "prec"[prod] :: mode[src] :: prod{'A; 'B} =
   slot{'A} `" * " slot{'B}

dform parens :: "prec"[prod] :: mode[prl] :: prod{'A; 'B} =
   slot{'A} times " " slot{'B}

dform parens :: "prec"[prod] :: mode[src] :: prod{'A; x. 'B['x]} =
   slot{'x} `":" slot{'A} `" * " slot{'B}

dform parens :: "prec"[prod] :: mode[prl] :: prod{'A; x. 'B['x]} =
   slot{'x} `":" slot{'A} times " " slot{'B}

dform mode[prl] :: pair{'a; 'b} =
   `"<" slot{'a}`"," slot{'b} `">"

dform parens :: "prec"[spread] :: mode[prl] :: spread{'e; u, v. 'b['u; 'v]} =
   `"let " pair{'u; 'v} `" = " slot{'e} `" in " slot{'b['u; 'v]}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext x:A * B
 * by productFormation A x
 * H >- A = A in Ui
 * H, x:A >- Ui ext B
 *)
prim productFormation 'H 'A 'x :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   ('B['x] : sequent ['ext] { 'H; x: 'A >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   x:'A * 'B['x]

(*
 * H >- x1:A1 * B1 = x2:A2 * B2 in Ui
 * by productEquality y
 * H >- A1 = A2 in Ui
 * H, y:A1 >- B1[y] = B2[y] in Ui
 *)
prim productEquality 'H 'y :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[@i:l] } -->
   sequent ['ext] { 'H >- x1:'A1 * 'B1['x1] = x2:'A2 * 'B2['x2] in univ[@i:l] } =
   it

(*
 * H >- x:A * B ext (a, b)
 * by pairFormation a y
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
prim pairFormation 'H 'a 'y :
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   ('b : sequent ['ext] { 'H >- 'B['a] }) -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- x:'A * 'B['x] } =
   'a, 'b

(*
 * H >- (a1, b1) = (a2, b2) in x:A * B
 * by pairEquality y
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B[a1]
 * H, y:A >- B[y] = B[y] in Ui
 *)
prim pairEquality 'H 'y :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B['a1] } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- ('a1, 'b1) = ('a2, 'b2) in x:'A * 'B } =
   it

(*
 * H, x:A * B[x], J[x] >- T[x] ext spread(x; u, v. t[u, v])
 * by productElimination u v
 * H, x:A * B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
prim productElimination 'H 'J 'z 'u 'v :
   ('t['u; 'v] : sequent ['ext] { 'H; z: x:'A * 'B; u: 'A; v: 'B['u]; 'J['u, 'v] >- 'T['u, 'v] }) -->
   sequent ['ext] { 'H; z: x:'A * 'B; 'J['z] >- 'T['z] } =
   spread{'z; u, v. 't['u; 'v]}

(*
 * H >- spread(e1; u1, v1. b1) = spread(e2; u2, v2. b2) in T[e1]
 * by spreadEquality (w:A * B)
 * H >- e1 = e2 in w:A * B
 * H, u:A, v: B[u], a: e1 = (u, v) in w:A * B >- b1[u; v] = b2[u; v] in T[u, v]
 *)
prim spreadEquality 'H lambda{z. 'T['z]} (w:'A * 'B['w]) 'u 'v 'a :
   sequent [squash] { 'H >- 'e1 = 'e2 in w:'A * 'B['w] } -->
   sequent [squash] { 'H; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >-
             'b1['u; 'v] = 'b2['u; 'v] in 'T['u, 'v] } -->
   sequent ['ext] { 'H >- spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T['e1] } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_dprod p =
   let t =
      try get_term_arg 1 p with
         Not_found -> raise (RefineError (StringError "d_concl_dprod: requires an argument"))
   in
   let count = hyp_count p in
   let y = get_opt_var_arg "y" p in
      (pairFormation count t y
       thenLT [addHiddenLabelT "wf";
               idT;
               addHiddenLabelT "wf"]) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_dprod i p =
   let a = get_term_arg 0 p in
   let count = hyp_count p in
   let i' = get_pos_hyp_index i count in
   let z = var_of_hyp i' p in
      (match maybe_new_vars ["u"; "v"] (declared_vars p) with
          [u; v] ->
             productElimination i' (count - i' - 1) z u v
        | _ ->
             failT) p

(*
 * Join them.
 *)
let d_dprod i =
   if i = 0 then
      d_concl_dprod
   else
      d_hyp_dprod i

let dprod_term = << x: 'A * 'B['x] >>

let d_resource = d_resource.resource_improve d_resource (dprod_term, d_dprod)
let d = d_resource.resource_extract d_resource

(*
 * EQCD.
 *)
let eqcd_dprod p =
   let count = hyp_count p in
   let v = get_opt_var_arg "y" p in
      (productEquality count v
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (dprod_term, eqcd_dprod)
let eqcd = eqcd_resource.resource_extract eqcd_resource

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:52:09  jyh
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
 * Revision 1.4  1996/10/23 15:18:06  jyh
 * First working version of dT tactic.
 *
 * Revision 1.3  1996/05/21 02:16:40  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:33:53  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/28 02:51:28  jyh
 * This is an initial version of the type theory.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
