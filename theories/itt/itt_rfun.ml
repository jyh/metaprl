(*
 * Dependent functions.
 *
 *)

include Tactic_type

include Itt_equal
include Itt_void
include Itt_set

open Printf
open Debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Resource

open Tactic_type
open Tacticals
open Sequent
open Var
open Typeinf
open Itt_void
open Itt_equal

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_rfun%t" eflush

(* debug_string DebugLoad "Loading itt_rfun..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(* declare "fun"{'A; 'B} *)
declare "fun"{'A; x. 'B['x]}
declare rfun{'A; f, x. 'B['f; 'x]}

declare lambda{x. 'b['x]}
declare apply{'f; 'a}

declare well_founded{'A; x, y. 'R['x; 'y]}
declare fix{f. 'b['f]}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_fun
prec prec_apply
prec prec_lambda
prec prec_lambda < prec_apply
prec prec_fun < prec_apply

dform fun_df1 : parens :: "prec"[prec_fun] :: "fun"{'A; 'B} =
   slot{'A} rightarrow " " slot{'B}

dform fun_df2 : parens :: "prec"[prec_fun] :: "fun"{'A; x. 'B['x]} =
   slot{bvar{'x}} `":" slot{'A} rightarrow " " slot{'B}

dform fun_df3 : rfun{'A; f, x. 'B['f; 'x]} =
   "{" " " slot{bvar{'f}} `"|" "fun"{'A; x. 'B['f; 'x]} "}"

dform apply_df1 : parens :: "prec"[prec_apply] :: apply{'f; 'a} =
   slot[lt]{'f} " " slot[le]{'a}

dform lambda_df1 : mode[prl] :: parens :: "prec"[prec_lambda] :: lambda{x. 'b} =
   Nuprl_font!lambda slot{'x} `"." slot{'b}

dform fix_df1 : mode[prl] :: fix{f. 'b} =
   `"fix" "(" slot{'f} `"." slot{'b} ")"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * apply(lambda(v. b[v]); a) -> b[a]
 *)
primrw reduceBeta : (lambda{v. 'b['v]} 'a) <--> 'b['a]
primrw reduceFix : fix{f. 'b['f]} <--> 'b[fix{f. 'b['f]}]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext { f | a:A -> B }
 * by rfunctionFormation { f | a: A -> B }
 *
 * H >- { f | a: A -> B } = { f | a: A -> B } in Ui
 *)
prim rfunctionFormation 'H { f | a: 'A -> 'B['f; 'a] } :
   sequent [squash] { 'H >- { f | a: 'A -> 'B['f; 'a] } = { f | a: 'A -> 'B['f; 'a] } in univ[@i:l] } :
   sequent ['ext] { 'H >- univ[@i:l] } =
   { f | a: 'A -> 'B['f; 'a] }

(*
 * H >- { f1 | a1:A1 -> B1[f1, a1] } = { f2 | a2:A2 -> B2[f2, a2] } in Ui
 * by rfunctionEquality R[a, b] g y z
 *
 * H >- A1 = A2 in Ui
 * H >- well_founded(A1; a, b. R[a, b])
 * H, y:A, g : { f1 | x1: { z: A1 | R z y } -> B1[f1, x1] } >- B1[g, y] = B2[g, y] in Ui
 *)
prim rfunctionEquality  'H lambda{a. lambda{b. 'R['a; 'b]}} 'g 'y 'z :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- well_founded{'A1; a, b. 'R['a; 'b]} } -->
   sequent [squash] { 'H;
             y: 'A1;
             g: { f1 | x1: { z: 'A1 | 'R['z; 'y] } -> 'B1['f1; 'x1] }
             >- 'B1['g; 'y] = 'B2['g; 'y] in univ[@i:l]
           } -->
   sequent ['ext] { 'H >- { f1 | a1:'A1 -> 'B1['f1; 'a1] }
                   = { f2 | a2:'A2 -> 'B2['f2; 'a2] }
                   in univ[@i:l]
           } =
   it

(*
 * H >- { f | a:A -> B[a] } ext lambda(y. fix(g. b[g, y]))
 * by rfunctionLambdaFormation R[a, b] g y z
 *
 * H >- A = A in Ui
 * H >- well_founded(A; a, b. R[a, b])
 * H, y: A, g: { f | { z: A | R z y } -> B[f, x] } >- B[g, y] ext b[g, y]
 *)
prim rfunction_lambdaFormation 'H lambda{a. lambda{b. 'R['a; 'b]}} 'g 'y 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- well_founded{'A; a, b. 'R['a; 'b]} } -->
   ('b['g; 'y] : sequent ['ext] { 'H; y: 'A; g: { f | x: { z: 'A | 'R['z; 'y] } -> 'B['f; 'x] } >- 'B['g; 'y] }) -->
   sequent ['ext] { 'H >- { f | x:'A -> 'B['f; 'x] } } =
   lambda{y. fix{g. 'b['g; 'y]}}

(*
 * H >- lambda(x1. b1[x1]) = lambda(x2. b2[x2]) in {f | x:A -> B[f, x] }
 * by rfunction_lambdaEquality y
 *
 * H >- { f | x:A -> B[f, x] } = { f | x:A -> B[f, x] } in type
 * H, y: A >- b1[y] = b2[y] in B[lambda(x1. b1[x1]); y]
 *)
prim rfunction_lambdaEquality 'H 'y :
   sequent [squash] { 'H >- "type"{{ f | x: 'A -> 'B['f; 'x] }} } -->
   sequent [squash] { 'H; y: 'A >- 'b1['y] = 'b2['y] in 'B[lambda{x1. 'b1['x1]}; 'y] } -->
   sequent ['ext] { 'H >- lambda{x1. 'b1['x1]} = lambda{x2. 'b2['x2]} in { f | x: 'A -> 'B['f; 'x] } } =
   it

(*
 * H >- f1 = f2 in { g | x:A -> B[g, x] }
 * by rfunctionExtensionality { g1 | x1:A1 -> B1[g1, x1] } { g2 | x2:A2 -> B2[g2, x2] } y
 *
 * H >- { g | x:A -> B[g, x] } = { g | x:A -> B[g, x] } in type
 * H, y: A >- f1 y = f2 y in B[f1, x]
 * H >- f1 = f1 in { g1 | x1:A1 -> B1[g1, x1] }
 * H >- f2 = f2 in { g2 | x2:A2 -> B2[g2, x2] }
 *)
prim rfunctionExtensionality 'H
        ({ g1 | x1:'A1 -> 'B1['g1; 'x1] })
        ({ g2 | x2:'A2 -> 'B2['g2; 'x2] })
        'y :
   sequent [squash] { 'H >- "type"{{ g | x:'A -> 'B['g; 'x] }} } -->
   sequent [squash] { 'H; y: 'A >- 'f1 'y = 'f2 'y in 'B['f1; 'x] } -->
   sequent [squash] { 'H >- 'f1 = 'f1 in { g1 | x1:'A1 -> 'B1['g1; 'x1] } } -->
   sequent [squash] { 'H >- 'f2 = 'f2 in { g2 | x2:'A2 -> 'B2['g2; 'x2] } } -->
   sequent ['ext] { 'H >- 'f1 = 'f2 in { g | x:'A -> 'B['g; 'x] } } =
   it

(*
 * H, f: { g | x:A -> B[g, x] }, J[f] >- T[f] ext t[f, f a, it]
 * by rfunctionElimination a y v
 *
 * H, f: { g | x:A -> B[g, x] }, J[f] >- a = a in A
 * H, f: { g | x:A -> B[g, x] }, J[f], y: B[f, a], v: y = f a in B[f, a] >- T[f] ext t[f, y, v]
 *)
prim rfunctionElimination 'H 'J 'f 'a 'y 'v :
   sequent [squash] { 'H; f: { g | x:'A -> 'B['g; 'x] }; 'J['f] >- 'a = 'a in 'A } -->
   ('t['f; 'y; 'v] : sequent ['ext] { 'H;
                               f: { g | x:'A -> 'B['g; 'x] };
                               'J['f];
                               y: 'B['f; 'a];
                               v: 'y = 'f 'a in 'B['f; 'a]
                               >- 'T['f] }) -->
   sequent ['ext] { 'H; f: { g | x:'A -> 'B['g; 'x] }; 'J['f] >- 'T['f] } =
   't['f; 'f 'a; it]

(*
 * H >- f1 a1 = f2 a2 in B[f1, a1]
 * by rfunction_applyEquality { f | x:A -> B[f, x] }
 *
 * H >- f1 = f2 in { f | x:A -> B[f, x] }
 * H >- a1 = a2 in A
 *)
prim rfunction_applyEquality 'H ({ f | x:'A -> 'B['f; 'x] }) :
   sequent [squash] { 'H >- 'f1 = 'f2 in { f | x:'A -> 'B['f; 'x] } } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- 'f1 'a1 = 'f2 'a2 in 'B['f1; 'a1] } =
   it

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

(*
 * Primitives.
 *)
let rfun_term = << { f | x: 'A -> 'B['f; 'x] } >>
let rfun_opname = opname_of_term rfun_term
let is_rfun_term = is_dep0_dep2_term rfun_opname
let dest_rfun = dest_dep0_dep2_term rfun_opname
let mk_rfun_term = mk_dep0_dep2_term rfun_opname

let well_founded_term = << well_founded{'A; x, y. 'R['x; 'y]} >>
let well_founded_opname = opname_of_term well_founded_term
let is_well_founded_term = is_dep0_dep2_term well_founded_opname
let dest_well_founded = dest_dep0_dep2_term well_founded_opname
let mk_well_founded_term = mk_dep0_dep2_term well_founded_opname

let lambda_term = << lambda{x. 'b['x]} >>
let lambda_opname = opname_of_term lambda_term
let is_lambda_term = is_dep1_term lambda_opname
let dest_lambda = dest_dep1_term lambda_opname
let mk_lambda_term = mk_dep1_term lambda_opname

let fix_term = << fix{x. 'b['x]} >>
let fix_opname = opname_of_term fix_term
let is_fix_term = is_dep1_term fix_opname
let dest_fix = dest_dep1_term fix_opname
let mk_fix_term = mk_dep1_term fix_opname

let apply_term = << apply{'f; 'a} >>
let apply_opname = opname_of_term apply_term
let is_apply_term = is_dep0_dep0_term apply_opname
let dest_apply = dest_dep0_dep0_term apply_opname
let mk_apply_term = mk_dep0_dep0_term apply_opname

let dfun_term = << x: 'A -> 'B['x] >>
let dfun_opname = opname_of_term dfun_term
let is_dfun_term = is_dep0_dep1_term dfun_opname
let dest_dfun = dest_dep0_dep1_term dfun_opname
let mk_dfun_term = mk_dep0_dep1_term dfun_opname

let fun_term = << 'A -> 'B >>
let fun_opname = opname_of_term fun_term
let is_fun_term = is_dep0_dep0_term fun_opname
let dest_fun = dest_dep0_dep0_term fun_opname
let mk_fun_term = mk_dep0_dep0_term fun_opname

(************************************************************************
 * D TACTICS                                                            *
 ************************************************************************)

(*
 * D the conclusion.
 * We take the WFounded(x, y) term as an optional argument.
 *)
let d_concl_rfun p =
   let wf =
      try get_with_arg p with
         Not_found -> raise (RefineError ("d_concl_rfun", StringError "need a well-order term"))
   in
   let t = goal p in
   let count = hyp_count p in
      (match maybe_new_vars ["g"; "y"; "z"] (declared_vars p) with
          [g; y; z] ->
             rfunction_lambdaFormation count wf g y z
             thenLT [addHiddenLabelT "wf";
                     addHiddenLabelT "aux";
                     idT]
        | _ ->
             raise (RefineError ("d_concl_rfun", StringError "not function type"))) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_rfun i p =
   let a = get_with_arg p in
   let i, j = hyp_indices p i in
   let f, _ = Sequent.nth_hyp p i in
      (match maybe_new_vars ["y"; "v"] (declared_vars p) with
          [y; v] ->
             rfunctionElimination i j f a y v
             thenLT [addHiddenLabelT "wf"; idT]
        | _ ->
             failT) p

(*
 * Join them.
 *)
let d_rfunT i =
   if i = 0 then
      d_concl_rfun
   else
      d_hyp_rfun i

let d_resource = d_resource.resource_improve d_resource (rfun_term, d_rfunT)

(************************************************************************
 * EQCD TACTICS                                                         *
 ************************************************************************)

(*
 * RFUN
 *
 * Need a term for the well-order.
 *)
let eqcd_rfunT p =
   let wf =
      try get_with_arg p with
         Not_found -> raise (RefineError ("eqcd_rfun", StringError "need a well-order term"))
   in
   let t = goal p in
   let count = hyp_count p in
      (match maybe_new_vars ["g"; "y"; "z"] (declared_vars p) with
          [g; y; z] ->
             rfunctionEquality count wf g y z
             thenT addHiddenLabelT "wf"
        | _ ->
             failT) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (rfun_term, eqcd_rfunT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_rfun inf decl t =
   let f, v, a, b = dest_rfun t in
   let decl', a' = inf decl a in
   let decl'', b' = inf ((v, a)::(f, mk_fun_term a void_term)::decl') b in
   let le1, le2 =
      try dest_univ a', dest_univ b' with
         Term.TermMatch _ -> raise (RefineError ("typeinf", StringTermError ("can't infer type for", t)))
   in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (rfun_term, inf_rfun)

(*
 * Type of lambda.
 *)
let inf_lambda (f : typeinf_func) (decl : term_subst) (t : term) =
   let v, b = dest_lambda t in
   let a = new_var v (List.map fst decl) in
   let decl', b' = f ((v, mk_var_term a)::decl) b in
   let decl'', a' =
      try decl', List.assoc a decl' with
         Not_found -> (a, void_term)::decl', void_term
   in
      decl'', mk_dfun_term v a' b'

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (lambda_term, inf_lambda)

(*
 * Type of apply.
 *)
let inf_apply inf decl t =
   let f, a = dest_apply t in
   let decl', f' = inf decl f in
   let decl'', a' = inf decl' a in
   let ty =
      if is_dfun_term f' then
         let v, d, r = dest_dfun f' in
            subst r [a] [v]
      else if is_fun_term f' then
         let _, r = dest_fun f' in
            r
      else if is_rfun_term f' then
         let f'', v, d, r = dest_rfun f' in
            subst r [f; a] [f''; v]
      else
         raise  (RefineError ("typeinf", StringTermError ("can't infer type for", t)))
   in
      decl'', ty

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (apply_term, inf_apply)

(*
 * $Log$
 * Revision 1.11  1998/06/15 22:33:31  jyh
 * Added CZF.
 *
 * Revision 1.10  1998/06/12 18:36:44  jyh
 * Working factorial proof.
 *
 * Revision 1.9  1998/06/12 13:47:36  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.8  1998/06/09 20:52:42  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.7  1998/06/01 13:56:13  jyh
 * Proving twice one is two.
 *
 * Revision 1.6  1998/05/28 13:47:58  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.5  1998/04/24 02:43:43  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.4  1998/04/22 22:45:05  jyh
 * *** empty log message ***
 *
 * Revision 1.3  1998/04/09 18:26:09  jyh
 * Working compiler once again.
 *
 * Revision 1.2  1997/08/06 16:18:38  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:23  jyh
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
 * Revision 1.4  1996/09/25 22:52:13  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.3  1996/05/21 02:17:06  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:12  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/30 01:37:17  jyh
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
