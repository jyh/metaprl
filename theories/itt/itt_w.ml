(*
 * W types.
 *)

include Itt_equal
include Itt_rfun

open Opname
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Sequent
open Var

open Itt_equal

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * W type is type of trees   (type w = a:A * (B[a] -> w))
 *)
declare w{'A; x. 'B['x]}

(*
 * Trees.  Each node has a label 'a, and a function to
 * compute the children 'f.
 *)
declare tree{'a; 'f}

(*
 * Induction over trees.
 *)
declare tree_ind{'z; a, f, g. 'body['a; 'f; 'g]}

(************************************************************************
 * REWRITING                                                            *
 ************************************************************************)

(*
 * Reduction rule.
 * The g part composes the label with an application to f.
 *)
primrw reduce_tree_ind :
   tree_ind{tree{'a1; 'f1}; a2, f2, g2. 'body['a2; 'f2; 'g2]}
   <--> 'body['a1; 'f1; lambda{a. lambda{b. tree_ind{.'f1 'a 'b; a2, f2, g2. 'body['a2; 'f2; 'g2]}}}]

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_w
prec prec_tree_ind

dform w_df : mode[prl] :: parens :: "prec"[prec_w] :: w{'A; x. 'B} =
   mathbbW slot{'x} `":" slot{'A} `"." slot{'B}

dform tree_df : mode[prl] :: tree{'a; 'f} =
   `"tree(" slot{'a} `"," " " slot{'f} `")"

dform tree_ind_df : mode[prl] :: parens :: "prec"[prec_tree_ind] :: tree_ind{'z; a, f, g. 'body} =
   szone pushm[3] `"tree_ind(" slot{'g} `"." " "
   pushm[3] `"let tree(" slot{'a} `", " slot{'f} `") =" space slot{'z} space `"in" popm space
   slot{'body} popm ezone

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext W(x:A; B[x])
 * by wFormation A x
 * H >- A = A in Ui
 * H, x:A >- Ui ext B
 *)
prim wFormation 'H 'A 'x :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   ('B['x] : sequent ['ext] { 'H; x: 'A >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   w{'A; x. 'B['x]}

(*
 * H >- W(x1:A1; B1) = W(x2:A2; B2) in Ui
 * by wEquality y
 * H >- A1 = A2 in Ui
 * H, y:A1 >- B1[y] = B2[y] in Ui
 *)
prim wEquality 'H 'y :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[@i:l] } -->
   sequent ['ext] { 'H >- w{'A1; x1. 'B1['x1]} = w{'A2; x2. 'B2['x2]} in univ[@i:l] } =
   it

(*
 * Typehood.
 *)
prim wType 'H 'x :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H; x: 'A1 >- "type"{'A2['x]} } -->
   sequent ['ext] { 'H >- "type"{.w{'A1; y.'A2['y]}} } =
   it

(*
 * H >- W(x:A; B[x]) ext tree(a, f)
 * by treeFormation a y
 * H >- a = a in A
 * H >- B[a] -> W(x:A; B[x]) ext f
 * H, y:A >- B[y] = B[y] in Ui
 *)
prim treeFormation 'H 'a 'y :
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   ('f : sequent ['ext] { 'H >- 'B['a] -> w{'A; x. 'B['x]} }) -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- w{'A; x. 'B['x]} } =
   tree{'a; 'f}

(*
 * H >- tree(a1, b1) = tree(a2, b2) in W(x:A; B)
 * by treeEquality y
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B[a1] -> W(x:A; B)
 * H, y:A >- B[y] = B[y] in Ui
 *)
prim treeEquality 'H 'y :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B['a1] -> w{'A; x. 'B['x]} } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- tree{'a1; 'b1} = tree{'a2; 'b2} in w{'A; x. 'B['x]} } =
   it

(*
 * H, x:W(y:A; B[y]), J[x] >- T[x] ext spread(x; u, v. t[u, v])
 * by wElimination u v
 * H, x:W(y:A; B[y]), u:A, v:B[u] -> W(y:A; B[y]), J[tree(u, v)] >- T[tree(u, v)] ext t[u, v]
 *)
prim wElimination 'H 'J 'z 'a 'f 'g 'a2 'b2 :
   ('t['z; 'a; 'f; 'g] :
   sequent ['ext] { 'H;
                    z: w{'A; x. 'B['x]};
                    'J['z];
                    a: 'A;
                    f: 'B['a] -> w{'A; x. 'B['x]};
                    g: a2: 'A -> b2: 'B['a2] -> 'T['f 'b2]
                  >- 'T[tree{'a; 'f}]
                  }) -->
   sequent ['ext] { 'H; z: w{'A; x. 'B['x]}; 'J['z] >- 'T['z] } =
      tree_ind{'z; a, f, g. 't['z; 'a; 'f; 'g]}

(*
 * Equality on tree induction forms.
 *)
prim tree_indEquality 'H (w{'A; x. 'B['x]}) 'a 'f 'g :
   sequent [squash] { 'H >- 'z1 = 'z2 in w{'A; x. 'B['x]} } -->
   sequent [squash] { 'H; a: 'A; f: 'B['a] -> w{'A; x. 'B['x]}; g: a: 'A -> 'B['a] -> 'T >-
      'body1['a; 'f; 'g] = 'body2['a; 'f; 'g] in 'T } -->
   sequent ['ext] { 'H >- tree_ind{'z1; a1, f1, g1. 'body1['a1; 'f1; 'g1]}
                          = tree_ind{'z2; a2, f2, g2. 'body2['a2; 'f2; 'g2]}
                          in 'T } =
   it

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let w_term = << w{'A; x. 'B['x]} >>
let w_opname = opname_of_term w_term
let is_w_term = is_dep0_dep1_term w_opname
let dest_w = dest_dep0_dep1_term w_opname
let mk_w_term = mk_dep0_dep1_term w_opname

let tree_term = << tree{'a; 'b} >>
let tree_opname = opname_of_term tree_term
let is_tree_term = is_dep0_dep0_term tree_opname
let dest_tree = dest_dep0_dep0_term tree_opname
let mk_tree_term = mk_dep0_dep0_term tree_opname

let tree_ind_term = << tree_ind{'e; u, v. 'b['u; 'v]} >>
let tree_ind_opname = opname_of_term tree_ind_term
let is_tree_ind_term = is_dep0_dep3_term tree_ind_opname
let dest_tree_ind = dest_dep0_dep3_term tree_ind_opname
let mk_tree_ind_term = mk_dep0_dep3_term tree_ind_opname

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_w p =
   let t =
      try get_with_arg p with
         Not_found ->
            raise (RefineError ("d_concl_w", StringError "requires an argument"))
   in
   let count = hyp_count p in
   let y = get_opt_var_arg "y" p in
      (treeFormation count t y
       thenLT [addHiddenLabelT "wf";
               idT;
               addHiddenLabelT "wf"]) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_w i p =
   let z, _ = Sequent.nth_hyp p i in
   let i, j = hyp_indices p i in
   let a, f, g, a2, b2 = maybe_new_vars5 p "a" "f" "g" "a" "b" in
      wElimination i j z a f g a2 b2 p

(*
 * Join them.
 *)
let d_wT i p =
   if i = 0 then
      d_concl_w p
   else
      d_hyp_w i p

let d_resource = d_resource.resource_improve d_resource (w_term, d_wT)

(*
 * Typehood.
 *)
let d_w_typeT i p =
   if i = 0 then
      let concl = Sequent.concl p in
      let v, _, _ = dest_w (one_subterm concl) in
      let v = maybe_new_vars1 p v in
         wType (hyp_count p) v p
   else
      raise (RefineError ("d_w_typeT", StringError "no elimination form"))

let type_w_term = << "type"{.w{'A1; x. 'A2['x]}} >>

let d_resource = d_resource.resource_improve d_resource (type_w_term, d_w_typeT)

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

(*
 * EQCD w.
 *)
let eqcd_wT p =
   let _, l, _ = dest_equal (concl p) in
   let v, _, _ = dest_w l in
   let x = get_opt_var_arg v p in
   let count = hyp_count p in
      (wEquality count x thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (w_term, eqcd_wT)

let w_equal_term = << w{'A1; x1. 'B1['x1]} = w{'A2; x2. 'B2['x2]} in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (w_equal_term, d_wrap_eqcd eqcd_wT)

(*
 * EQCD pair.
 *)
let eqcd_treeT p =
   let l, _, _ = dest_equal (concl p) in
   let v, _, _ = dest_w l in
   let x = get_opt_var_arg v p in
   let count = hyp_count p in
      (treeEquality count x thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (tree_term, eqcd_treeT)

let tree_equal_term = << tree{'a1; 'b1} = tree{'a2; 'b2} in w{'A; x. 'B['x]} >>

let d_resource = d_resource.resource_improve d_resource (tree_equal_term, d_wrap_eqcd eqcd_treeT)

(*
 * EQCD spread.
 *)
let eqcd_tree_indT p =
   let _, l, _ = dest_equal (concl p) in
   let a, f, g, _, _ = dest_tree_ind l in
   let a, f, g = maybe_new_vars3 p a f g in
   let w =
      try get_type_arg p "type" with
         Not_found ->
            raise (RefineError ("eqcd_tree_indT", StringError "requires a type argument"))
   in
      tree_indEquality (hyp_count p) w a f g p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (tree_ind_term, eqcd_tree_indT)

let tree_ind_equal_term = << tree_ind{'z1; a1, f1, g1. 'body1['a1; 'f1; 'g1]}
                           = tree_ind{'z2; a2, f2, g2. 'body2['a2; 'f2; 'g2]}
                           in 'T >>

let d_resource = d_resource.resource_improve d_resource (tree_ind_equal_term, d_wrap_eqcd eqcd_tree_indT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_w f decl t =
   let v, a, b = dest_w t in
   let decl', a' = f decl a in
   let decl'', b' = f ((v, a)::decl') b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (w_term, inf_w)

(*
 * Type of pair.
 * This will be pretty difficult.
 *)
let inf_tree f decl t =
   let a, b = dest_tree t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
      decl'', mk_w_term "v" a' b'

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (tree_term, inf_tree)

(*
 * Type of tree_ind.
let inf_tree_ind inf decl t =
   let a, f, g, z, b = dest_tree_ind t in
   let decl', a' = inf decl a in
      if is_w_term a' then
         let x, l, r = dest_w a' in
            inf ((a, l)::(f, subst r [mk_var_term u] [x])::decl') b
      else
         raise (RefineError ("typeinf", StringTermError ("can't infer type for", t)))

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (tree_ind_term, inf_tree_ind)
 *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
