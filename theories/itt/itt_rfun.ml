(*
 * Dependent functions.
 *
 *)

open Debug
open Refine_sig
open Resource

include Var

include Itt_equal
include Itt_set

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

dform parens :: "prec"[prec_fun] :: "fun"{'A; 'B} =
   slot{'A} rightarrow " " slot{'B}

dform parens :: "prec"[prec_fun] :: "fun"{'A; x. 'B['x]} =
   slot{bvar{'x}} `":" slot{'A} rightarrow " " slot{'B}

dform rfun{'A; f, x. 'B['f; 'x]} =
   "{" " " slot{bvar{'f}} `"|" "fun"{'A; x. 'B['f; 'x]} "}"

dform parens :: "prec"[prec_apply] :: apply{'f; 'a} =
   slot[lt]{'f} " " slot[le]{'a}

dform mode[prl] :: parens :: "prec"[prec_lambda] :: lambda{x. 'b['x]} =
   Nuprl_font!lambda slot{'x} `"." slot{'b['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * apply(lambda(v. b[v]); a) -> b[a]
 *)
primrw betaReduction : (lambda{v. 'b['v]} 'a) <--> 'b['a]
primrw fix : fix{f. 'b['f]} <--> 'b[fix{f. 'b['f]}]

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
   't

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
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D the conclusion.
 * We take the WFounded(x, y) term as an optional argument.
 *)
let d_concl_rfun p =
   let wf =
      try get_term_arg 0 p with
         Not_found -> raise (RefineError (StringError "d_concl_rfun: need a well-order term"))
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
             raise (RefineError (StringError "d_concl_rfun: not function type"))) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_rfun i p =
   let a = get_term_arg 0 p in
   let count = hyp_count p in
   let i' = get_pos_hyp_index i count in
   let f = var_of_hyp i' p in
      (match maybe_new_vars ["y"; "v"] (declared_vars p) with
          [y; v] ->
             rfunctionElimination i' (count - i' - 1) f a y v
             thenLT [addHiddenLabelT "wf"; idT]
        | _ ->
             failT) p

(*
 * Join them.
 *)
let d_rfun i =
   if i = 0 then
      d_concl_rfun
   else
      d_hyp_rfun i

let rfun_term = << { f | x: 'A -> 'B['f; 'x] } >>

let d_resource = d_resource.resource_improve d_resource (rfun_term, d_rfun)
let d = d_resource.resource_extract d_resource

(*
 * EQCD.
 *
 * Need a term for the well-order.
 *)
let eqcd_rfun p =
   let wf =
      try get_term_arg 0 p with
         Not_found -> raise (RefineError (StringError "eqcd_rfun: need a well-order term"))
   in
   let t = goal p in
   let count = hyp_count p in
      (match maybe_new_vars ["g"; "y"; "z"] (declared_vars p) with
          [g; y; z] ->
             rfunctionEquality count wf g y z
             thenT addHiddenLabelT "wf"
        | _ ->
             failT) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (rfun_term, eqcd_rfun)
let eqcd = eqcd_resource.resource_extract eqcd_resource

(*
 * $Log$
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
