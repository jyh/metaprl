(*
 * This interpretation of CZF is derived from Aczel's
 * paper "The Type Theoretic Interpretation of Constructive
 * Set Theory: Inductive Definitions," Logic, Methodology
 * and Philosophy of Science VII, Barcan Marcus et. al. eds.,
 * Elsevier 1986 17--49.
 *
 * The "set" type is used to relate CZF to the Nuprl type theory.
 * We use a W-type over "small" types to define sets.
 *
 *    type set = W(x:small. x)
 *
 * Where the type small is defined inductively:
 *       1. int
 *
 *    If A, B in small, then so are:
 *       2. fun{A; x.B[x]}
 *       3. exists{A; x.B[x]}
 *       4. union{A; B}
 *       5. equal{A; a; b}
 *
 * We assert the existence of a small type with
 * an elimination forms.
 *
 *    NOTE: We may want to get stronger elimination
 *    forms by using the following definition:
 *
 *       type set = W(x:small_desc. small_comp x)
 *
 *    The type small_desc is an index type of descriptions
 *    of small types, and (small_comp: small_desc -> small) is
 *    a bijection.
 *
 * We abbreviate the sets themselves as:
 *    collect{T; x. a[x]} = tree{T; lambda x. a[x]}
 *
 * This interpretation justifies Aczel's construction:
 *
 *          H >- T in small     H, x:T >- a[x] in set
 *          -----------------------------------------
 *               H >- collect{T; x. a[x]} in set
 *)

include Itt_theory
include Czf_itt_small

open Refiner.Refiner.Term

open Tacticals
open Conversionals

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
rewrite unfold_wf : wf{'p} <--> "type"{'p}
rewrite unfold_restricted : restricted{x. 'P['x]} <-->
   ((all x: set. small_type{'P['x]})
    & (all a: set. exst b: set. all z: set. "iff"{member{'z; 'b}; .member{'z; 'a} & 'P['z]}))

rewrite unfold_set : set <--> w{small; x. 'x}
rewrite unfold_isset : isset{'s} <--> ('s = 's in set)
rewrite unfold_member : member{'x; 'y} <-->
  (('x = 'x in set)
   & ('y = 'y in set)
   & set_ind{'y; t, f, g. "exists"{'t; a. 'f 'a = 'x in set}})
rewrite unfold_collect : collect{'T; x. 'a['x]} <--> tree{'T; lambda{x. 'a['x]}}
rewrite unfold_set_ind : set_ind{'s; x, f, g. 'b['x; 'f; 'g]} <-->
   tree_ind{'s; x, f, g. 'b['x; 'f; 'g]}

rewrite reduce_set_ind :
   set_ind{collect{'T; x. 'a['x]}; a, f, g. 'b['a; 'f; 'g]}
   <--> 'b['T; lambda{x. 'a['x]}; lambda{a2. lambda{b2. set_ind{.'a['a2] 'b2; a, f, g. 'b['a; 'f; 'g]}}}]

rewrite reduce_member :
   member{'x; collect{'T; y. 'f['y]}} <-->
      isset{'x} & isset{collect{'T; y. 'f['y]}} & "exists"{'T; z. 'f['z] = 'x in set}

val fold_wf : conv
val fold_restricted : conv

val fold_set : conv
val fold_isset : conv
val fold_member : conv
val fold_collect : conv
val fold_set_ind : conv

(************************************************************************
 * RELATION TO ITT                                                      *
 ************************************************************************)

(*
 * We need the property that every well-formed proposition
 * is a type.  The proof is delayed until the theory is collected
 * and an induction form is given for well-formed formulas.
 *)
axiom wf_type 'H :
   sequent ['ext] { 'H >- wf{'T} } -->
   sequent ['ext] { 'H >- "type"{'T} }

(*
 * A set is a type in ITT.
 *)
axiom set_type 'H :
   sequent ['ext] { 'H >- "type"{set} }

(*
 * Membership judgment is also a type.
 *)
axiom member_type 'H :
   sequent ['ext] { 'H >- isset{'t} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- "type"{member{'a; 't}} }

(*
 * Equality from sethood.
 *)
axiom equal_set 'H :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- 's = 's in set }

(************************************************************************
 * SET TYPE                                                             *
 ************************************************************************)

(*
 * By assumption.
 *)
axiom isset_assum 'H 'J :
   sequent ['ext] { 'H; x: set; 'J['x] >- isset{'x} }

(*
 * Elements of a set are also sets.
 *)
axiom isset_member 'H 'y :
   sequent ['ext] { 'H >- member{'x; 'y} } -->
   sequent ['ext] { 'H >- isset{'x} }

(*
 * Only sets have elements.
 *)
axiom isset_contains 'H 'x :
   sequent ['ext] { 'H >- member{'x; 'y} } -->
   sequent ['ext] { 'H >- isset{'y} }

(*
 * This is how a set is constructed.
 *)
axiom isset_collect 'H 'y :
   sequent ['ext] { 'H >- small_type{'T} } -->
   sequent ['ext] { 'H; y: 'T >- isset{'a['y]} } -->
   sequent ['ext] { 'H >- isset{collect{'T; x. 'a['x]}} }

(*
 * Induction.
 *)
axiom set_elim 'H 'J 'a 'T 'f 'w :
   sequent ['ext] { 'H;
                    a: set;
                    'J['a];
                    T: small;
                    f: 'T -> set;
                    w: (all x : 'T. 'C['f 'x])
                  >- 'C[collect{'T; x. 'f 'x}]
                  } -->
   sequent ['ext] { 'H; a: set; 'J['a] >- 'C['a] }

axiom set_elim2 'H 'J 'a 'T 'f 'w 'z :
   sequent ['ext] { 'H;
                    a: set;
                    'J['a];
                    T: small;
                    f: 'T -> set;
                    w: (all x : 'T. 'C['f 'x]);
                    z: isset{collect{'T; x. 'f 'x}}
                  >- 'C[collect{'T; x. 'f 'x}]
                  } -->
   sequent ['ext] { 'H; a: set; 'J['a] >- 'C['a] }

(*
 * Equality on tree induction forms.
 *)
axiom set_ind_equality 'H 'A (bind{x.'B['x]}) 'a 'f 'g :
   sequent [squash] { 'H >- 'z1 = 'z2 in set } -->
   sequent [squash] { 'H; a: 'A; f: 'B['a] -> set; g: a: 'A -> 'B['a] -> 'T >-
      'body1['a; 'f; 'g] = 'body2['a; 'f; 'g] in 'T } -->
   sequent ['ext] { 'H >- set_ind{'z1; a1, f1, g1. 'body1['a1; 'f1; 'g1]}
                          = set_ind{'z2; a2, f2, g2. 'body2['a2; 'f2; 'g2]}
                          in 'T }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * wf{'T} => type{'T}
 *)
val wfTypeT : tactic

(*
 * isset{'s} => 's = 's in set
 *)
val eqSetT : tactic

(*
 * H, x: set, J >- isset{x}
 *)
val assumSetT : int -> tactic
val setAssumT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
