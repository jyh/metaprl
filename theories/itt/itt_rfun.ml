(*
 * Dependent functions.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *
 *)

include Tacticals

include Itt_equal
include Itt_void
include Itt_set

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tacticals
open Conversionals
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
prec prec_fun < prec_lambda

dform fun_df1 : parens :: "prec"[prec_fun] :: "fun"{'A; 'B} =
   slot{'A} " " rightarrow " " slot{'B}

dform fun_df2 : parens :: "prec"[prec_fun] :: "fun"{'A; x. 'B['x]} =
   slot{bvar{'x}} `":" slot{'A} " " rightarrow " " slot{'B}

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

let reduce_info =
   [<< (lambda{v. 'b['v]} 'a) >>, reduceBeta;
    << fix{f. 'b['f]} >>, reduceFix]

let reduce_resource = add_reduce_info reduce_resource reduce_info

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
   let count = hyp_count_addr p in
   let g, y, z = maybe_new_vars3 p "g" "y" "z" in
       (rfunction_lambdaFormation count wf g y z
        thenLT [addHiddenLabelT "wf";
                addHiddenLabelT "aux";
                idT]) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_rfun i p =
   let a = get_with_arg p in
   let f, _ = Sequent.nth_hyp p i in
   let j, k = hyp_indices p i in
   let y, v = maybe_new_vars2 p "y" "v" in
       (rfunctionElimination j k f a y v
        thenLT [addHiddenLabelT "wf"; idT]) p

(*
 * Join them.
 *)
let d_rfunT i =
   if i = 0 then
      d_concl_rfun
   else
      d_hyp_rfun i

let d_resource = Mp_resource.improve d_resource (rfun_term, d_rfunT)

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
   let count = hyp_count_addr p in
   let g, y, z = maybe_new_vars3 p "g" "y" "z" in
       (rfunctionEquality count wf g y z
        thenT addHiddenLabelT "wf") p

let eqcd_resource = Mp_resource.improve eqcd_resource (rfun_term, eqcd_rfunT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_rfun inf decl t =
   let f, v, a, b = dest_rfun t in
   let decl', a' = inf decl a in
   let decl'', b' = inf (add_unify_subst v a (add_unify_subst f (mk_fun_term a void_term) decl')) b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = Mp_resource.improve typeinf_resource (rfun_term, inf_rfun)

(*
 * Type of lambda.
 *)
let inf_lambda (f : typeinf_func) (decl : unify_subst) (t : term) =
   let v, b = dest_lambda t in
   let a = new_unify_var decl v in
   let decl', b' = f (add_unify_subst v (mk_var_term a) decl) b in
   let decl'', a' =
(*
      try decl', List.assoc a decl' with
         Not_found ->
*)
            (add_unify_subst a void_term decl'), void_term
   in
      decl'', mk_dfun_term v a' b'

let typeinf_resource = Mp_resource.improve typeinf_resource (lambda_term, inf_lambda)

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

let typeinf_resource = Mp_resource.improve typeinf_resource (apply_term, inf_apply)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
