(*
 * The "set" type is used to relate CZF to the Nuprl type theory.
 * The set type is defined inductively.
 *    The base types are:
 *       1. int
 *       2. fun{A; x.B[x]}
 *       3. exists{A; x.B[x]}
 *       4. union{A; B}
 *       5. equal{A; a; b}
 *
 *    The inductive construction is given by rule:
 *       6. H >- T in U1         H, x:T >- a in set
 *          -------------------------------------
 *               H >- collect{T; x. a[x]} in set
 *
 * We could define this set recursively.  Instead, we define it
 * as a collection of rules.
 *)

include Itt_theory
include Czf_itt_small

open Printf
open Debug

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Resource
open Term_stable

open Tacticals
open Tacticals
open Conversionals
open Sequent
open Var

open Itt_equal
open Itt_rfun
open Itt_dprod
open Itt_union
open Itt_w

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_equal%t" eflush

let debug_czf_set =
   create_debug (**)
      { debug_name = "czf_set";
        debug_description = "display czf_set operations";
        debug_value = false
      }

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Well-formedness judgements on propositions,
 * and restricted propositions do not range over
 * all sets.
 *    wf{'p}: 'p is a well-formed proposition in CZF
 *    restricted{'p}: 'p is a well-formed restricted proposition in CZF
 *       where restricted means that it contains no unbounded
 *       set quantifications.
 *)
declare wf{'p}
declare restricted{x. 'P['x]}

(*
 * Sets are built by collecting over small types.
 *   set: the type of all sets
 *   isset{'s}: the judgement that 's is a set
 *   member{'x; 't}:
 *      a. 'x is a set
 *      b. 't is a set
 *      c. 'x is an element of 't
 *   collect{'T; x. 'a['x]}:
 *      the set constructed from the family of sets 'a['x]
 *      where 'x ranges over 'T
 *)
declare set
declare isset{'s}
declare member{'x; 't}
declare collect{'T; x. 'a['x]}
declare set_ind{'s; x, f, g. 'b['x; 'f; 'g]}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Sets.
 *)
primrw unfold_wf : wf{'p} <--> "type"{'p}
primrw unfold_restricted : restricted{x. 'P['x]} <-->
   ((all x: small. small_type{'P['x]})
    & (all a: set. exst b: set. all z: set. "iff"{member{'z; 'b}; .member{'z; 'a} & 'P['z]}))

primrw unfold_set : set <--> w{small; x. 'x}
primrw unfold_isset : isset{'s} <--> ('s = 's in set)
primrw unfold_member : member{'x; 'y} <-->
  (('x = 'x in set)
   & ('y = 'y in set)
   & tree_ind{'y; t, f, g. "exists"{'t; a. 'f 'a = 'x in set}})
primrw unfold_collect : collect{'T; x. 'a['x]} <--> tree{'T; lambda{x. 'a['x]}}
primrw unfold_set_ind : set_ind{'s; x, f, g. 'b['x; 'f; 'g]} <-->
   tree_ind{'s; x, f, g. 'b['x; 'f; 'g]}

interactive_rw reduce_set_ind :
   set_ind{collect{'T; x. 'a['x]}; a, f, g. 'b['a; 'f; 'g]}
   <--> 'b['T; lambda{x. 'a['x]}; lambda{a2. lambda{b2. set_ind{.'a['a2] 'b2; a, f, g. 'b['a; 'f; 'g]}}}]

interactive_rw reduce_member :
   member{'x; collect{'T; y. 'f['y]}} <-->
      isset{'x} & isset{collect{'T; y. 'f['y]}} & "exists"{'T; z. 'f['z] = 'x in set}

let fold_wf         = makeFoldC << wf{'p} >> unfold_wf
let fold_restricted = makeFoldC << restricted{x. 'P['x]} >> unfold_restricted

let fold_set        = makeFoldC << set >> unfold_set
let fold_isset      = makeFoldC << isset{'t} >> unfold_isset
let fold_member     = makeFoldC << member{'x; 'y} >> unfold_member
let fold_collect    = makeFoldC << collect{'T; x. 'a['x]} >> unfold_collect
let fold_set_ind    = makeFoldC << set_ind{'s; a, f, g. 'b['a; 'f; 'g]} >> unfold_set_ind

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform wf_df : mode[prl] :: parens :: "prec"[prec_apply] :: wf{'A} =
   slot{'A} `" wf"

dform restricted_df : mode[prl] :: parens :: "prec"[prec_apply] :: restricted{x. 'P} =
   slot{'P} `" restricted"

dform set_df : set =
   `"set"

dform isset_df : mode[prl] :: parens :: "prec"[prec_apply] :: isset{'s} =
   slot{'s} `" set"

dform member_df : mode[prl] :: parens :: "prec"[prec_apply] :: member{'x; 't} =
   slot{'x} " " Nuprl_font!member " " slot{'t}

dform collect_df : mode[prl] :: parens :: "prec"[prec_apply] :: collect{'T; x. 'a} =
   szone pushm[3] `"collect" " " slot{'x} `":" " " slot{'T} `"." " " slot{'a} popm ezone

dform set_ind_df : mode[prl] :: parens :: "prec"[prec_tree_ind] :: set_ind{'z; a, f, g. 'body} =
   szone pushm[3] `"set_ind(" slot{'g} `"." " "
   pushm[3] `"let tree(" slot{'a} `", " slot{'f} `") =" space slot{'z} space `"in" popm space
   slot{'body} popm ezone

(************************************************************************
 * RELATION TO ITT                                                      *
 ************************************************************************)

(*
 * We need the property that every well-formed proposition
 * is a type.  The proof is delayed until the theory is collected
 * and an induction form is given for well-formed formulas.
 *)
interactive wf_type 'H :
   sequent ['ext] { 'H >- wf{'T} } -->
   sequent ['ext] { 'H >- "type"{'T} }

(*
 * A set is a type in ITT.
 *)
interactive set_type 'H : :
   sequent ['ext] { 'H >- "type"{set} }

(*
 * Membership judgment is also a type.
 *)
interactive member_type 'H :
   sequent ['ext] { 'H >- isset{'t} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- "type"{member{'a; 't}} }

(*
 * Equality from sethood.
 *)
interactive equal_set 'H :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- 's = 's in set }

(************************************************************************
 * SET TYPE                                                             *
 ************************************************************************)

(*
 * By assumption.
 *)
interactive isset_assum 'H 'J : :
   sequent ['ext] { 'H; x: set; 'J['x] >- isset{'x} }

(*
 * Only sets have elements.
 *)
interactive isset_contains 'H 'x :
   sequent ['ext] { 'H >- member{'x; 'y} } -->
   sequent ['ext] { 'H >- isset{'y} }

(*
 * Elements of a set are also sets.
 *)
interactive isset_member 'H 'y :
   sequent ['ext] { 'H >- member{'x; 'y} } -->
   sequent ['ext] { 'H >- isset{'x} }

(*
 * This is how a set is constructed.
 *)
interactive isset_collect 'H 'y :
   sequent ['ext] { 'H >- small_type{'T} } -->
   sequent ['ext] { 'H; y: 'T >- isset{'a['y]} } -->
   sequent ['ext] { 'H >- isset{collect{'T; x. 'a['x]}} }

(*
 * Induction.
 *)
interactive set_elim 'H 'J 'a 'T 'f 'w :
   sequent ['ext] { 'H;
                    a: set;
                    'J['a];
                    T: small;
                    f: 'T -> set;
                    w: (all x : 'T. 'C['f 'x])
                  >- 'C[collect{'T; x. 'f 'x}]
                  } -->
   sequent ['ext] { 'H; a: set; 'J['a] >- 'C['a] }

(*
 * Equality on tree induction forms.
 *)
interactive set_ind_equality 'H 'A (bind{x.'B['x]}) 'a 'f 'g :
   sequent [squash] { 'H >- 'z1 = 'z2 in set } -->
   sequent [squash] { 'H; a: 'A; f: 'B['a] -> set; g: a: 'A -> 'B['a] -> 'T >-
      'body1['a; 'f; 'g] = 'body2['a; 'f; 'g] in 'T } -->
   sequent ['ext] { 'H >- set_ind{'z1; a1, f1, g1. 'body1['a1; 'f1; 'g1]}
                          = set_ind{'z2; a2, f2, g2. 'body2['a2; 'f2; 'g2]}
                          in 'T }

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let int_opname = opname_of_term Itt_int.int_term
let fun_opname = opname_of_term Itt_rfun.fun_term
let prod_opname = opname_of_term Itt_dprod.dprod_term
let union_opname = opname_of_term Itt_union.union_term
let equal_opname = opname_of_term Itt_equal.equal_term

let wf_term = << wf{'a} >>
let restricted_term = << restricted{x. 'P['x]} >>
let wf_opname = opname_of_term wf_term
let restricted_opname = opname_of_term restricted_term

let set_term = << set >>
let isset_term = << isset{'s} >>
let member_term = << member{'x; 't} >>
let collect_term = << collect{'T; x. 'a['x]} >>

let isset_opname = opname_of_term isset_term
let member_opname = opname_of_term member_term
let collect_opname = opname_of_term collect_term

(*
 * Testers.
 *)
let is_wf_term =
   is_dep0_term wf_opname

let is_restricted_term =
   is_dep1_term restricted_opname

let is_isset_term =
   is_dep0_term isset_opname

let is_member_term =
   is_dep0_dep0_term member_opname

let is_collect_term =
   is_dep0_dep1_term collect_opname

(*
 * Constructors.
 *)
let mk_wf_term =
   mk_dep0_term wf_opname

let mk_restricted_term =
   mk_dep1_term restricted_opname

let mk_isset_term =
   mk_dep0_term isset_opname

let mk_member_term =
   mk_dep0_dep0_term member_opname

let mk_collect_term =
   mk_dep0_dep1_term collect_opname

(*
 * Destructors.
 *)
let dest_wf =
   dest_dep0_term wf_opname

let dest_restricted =
   dest_dep1_term restricted_opname

let dest_isset =
   dest_dep0_term isset_opname

let dest_member =
   dest_dep0_dep0_term member_opname

let dest_collect t =
   dest_dep0_dep1_term collect_opname

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Collect is a set.
 *)
let d_isset_genT tac i p =
   if i = 0 then
      let i = hyp_count p in
         try
            let arg = get_with_arg p in
            let i =
               try get_sel_arg p with
                  RefineError _ ->
                     1
            in
               if i > 1 then
                  isset_member i arg p
               else
                  isset_contains i arg p
         with
            RefineError _ ->
               tac i p
   else
      raise (RefineError ("d_issetT", StringError "no elimination rule for isset"))

let d_isset_varT i p =
   let tac i p =
      raise (RefineError ("d_issetT", StringError "use withT to provide an argument"))
   in
      d_isset_genT tac i p

let d_isset_collectT i p =
   let tac i p =
      let v = maybe_new_vars1 p "v" in
         isset_collect i v p
   in
      d_isset_genT tac i p

(*
 * Special case for collection.
 *)
let isset_collect_term = << isset{collect{'T; x. 'a['x]}} >>

let d_resource = d_resource.resource_improve d_resource (isset_term, d_isset_varT)
let d_resource = d_resource.resource_improve d_resource (isset_collect_term, d_isset_collectT)

(************************************************************************
 * OTHER TACTICS                                                        *
 ************************************************************************)

(*
 * H >- set type
 *)
let d_set_typeT i p =
   if i = 0 then
      set_type (Sequent.hyp_count p) p
   else
      raise (RefineError ("d_set_typeT", StringError "no elimination rule"))

let set_type_term = << "type"{set} >>

let d_resource = d_resource.resource_improve d_resource (set_type_term, d_set_typeT)

(*
 * H >- member{a; t} type
 *)
let d_member_typeT i p =
   if i = 0 then
      member_type (Sequent.hyp_count p) p
   else
      raise (RefineError ("d_member_typeT", StringError "no elimination rule"))

let member_type_term = << "type"{member{'a; 't}} >>

let d_resource = d_resource.resource_improve d_resource (member_type_term, d_member_typeT)

(*
 * Set elimination.
 *)
let d_setT i p =
   if i = 0 then
      raise (RefineError ("d_setT", StringTermError ("no formation rule", set_term)))
   else
      let v_a, _ = nth_hyp p i in
      let i, j = hyp_indices p i in
      let v_T, v_f, v_b = maybe_new_vars3 p "T" "f" "b" in
         set_elim i j v_a v_T v_f v_b p

let d_resource = d_resource.resource_improve d_resource (set_term, d_setT)

(*
 * Apply the type rule.
 *)
let wfTypeT p =
   wf_type (Sequent.hyp_count p) p

(*
 * Equal sets.
 *)
let eqSetT p =
   equal_set (hyp_count p) p

(*
 * Assumption.
 *)
let setAssumT i p =
   let i, j = hyp_indices p i in
      isset_assum i j p

let assumSetT = setAssumT

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
