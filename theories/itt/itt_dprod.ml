(*
 * Rules for dependent product.
 *
 *)

open Debug
open Term
open Options
open Refine_sig
open Resource
open Refine_sig

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

(*
 * H >- a1:A1 * B1 <= a2:A2 * B2
 * by functionSubtype
 *
 * H >- A1 <= A2
 * H, a: A1 >- B1[a] <= B2[a]
 *)
prim productSubtype 'H 'a :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { 'H >- subtype{ (a1:'A1 * 'B1['a1]); (a2:'A2 * 'B2['a2]) } } =
   it

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let dprod_term = << x: 'A * 'B['x] >>
let dprod_opname = opname_of_term dprod_term
let is_dprod_term = is_dep0_dep1_term dprod_opname
let dest_dprod = dest_dep0_dep1_term dprod_opname
let mk_dprod_term = mk_dep0_dep1_term dprod_opname

let prod_term = << 'A * 'B >>
let prod_opname = opname_of_term prod_term
let is_prod_term = is_dep0_dep0_term prod_opname
let dest_prod = dest_dep0_dep0_term prod_opname
let mk_prod_term = mk_dep0_dep0_term prod_opname

let pair_term = << pair{'a; 'b} >>
let pair_opname = opname_of_term pair_term
let is_pair_term = is_dep0_dep0_term pair_opname
let dest_pair = dest_dep0_dep0_term pair_opname
let mk_pair_term = mk_dep0_dep0_term pair_opname

let spread_term = << spread{'e; u, v. 'b['u; 'v]} >>
let spread_opname = opname_of_term spread_term
let is_spread_term = is_dep0_dep2_term spread_opname
let dest_spread = dest_dep0_dep2_term spread_opname
let mk_spread_term = mk_dep0_dep2_term spread_opname

(************************************************************************
 * D TACTIC                                                             *
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
let d_dprodT i =
   if i = 0 then
      d_concl_dprod
   else
      d_hyp_dprod i

let d_resource = d_resource.resource_improve d_resource (dprod_term, d_dprodT)

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

(*
 * EQCD dprod.
 *)
let eqcd_dprodT p =
   let _, l, _ = dest_equal (concl p) in
   let v, _, _ = dest_dprod l in
   let x = get_opt_var_arg v p in
   let count = hyp_count p in
      (productEquality count x
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (dprod_term, eqcd_dprodT)

(*
 * EQCD pair.
 *)
let eqcd_pairT p =
   let l, _, _ = dest_equal (concl p) in
   let v, _, _ = dest_dprod l in
   let x = get_opt_var_arg v p in
   let count = hyp_count p in
      (pairEquality count x
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (pair_term, eqcd_pairT)

(*
 * EQCD spread.
 *)
let eqcd_spreadT p =
   let _, l, _ = dest_equal (concl p) in
   let u, v, _, _ = dest_spread l in
      raise (RefineError (StringError "eqcd_spreadT: not implemented"))

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (spread_term, eqcd_spreadT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_dprod f decl t =
   let v, a, b = dest_dprod t in
   let decl', a' = f decl a in
   let decl'', b' = f ((v, a)::decl') b in
   let le1, le2 =
      try dest_univ a', dest_univ b' with
         Term.TermMatch _ -> raise (RefineError (StringTermError ("typeinf: can't infer type for", t)))
   in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (dprod_term, inf_dprod)

(*
 * Type of pair.
 *)
let inf_pair f decl t =
   let a, b = dest_pair t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
      decl'', mk_prod_term a' b'

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (pair_term, inf_pair)

(*
 * Type of spread.
 *)
let inf_spread inf decl t =
   let u, v, a, b = dest_spread t in
   let decl', a' = inf decl a in
      if is_prod_term a' then
         let l, r = dest_prod a' in
            inf ((u, l)::(v, r)::decl') b
      else if is_dprod_term a' then
         let x, l, r = dest_dprod a' in
            inf ((u, l)::(v, subst r [mk_var_term u] [x])::decl') b
      else
         raise (RefineError (StringTermError ("typeinf: can't infer type for", t)))

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (spread_term, inf_spread)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let dprod_subtypeT p =
   let a = get_opt_var_arg "x" p in
      (productSubtype (hyp_count p) a
       thenT addHiddenLabelT "subtype") p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (DSubtype ([<< a1:'A1 * 'B1['a1] >>, << a2:'A2 * 'B2['a2] >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              dprod_subtypeT))

(*
 * $Log$
 * Revision 1.2  1997/08/06 16:18:25  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
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
