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
declare restricted{'p}

(*
 * These are the small types from which sets are built.
 *    small: the type of small propositions
 *    small_desc: descriptions of small propositions
 *
 *)
declare small
declare small_type{'t}

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

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Sets.
 *)
rewrite unfold_small_type : small_type{'t} <--> ('t = 't in small)
rewrite unfold_set : set <--> w{small; x. 'x}
rewrite unfold_isset : isset{'s} <--> ('s = 's in set)
rewrite unfold_member : member{'x; 'y} <-->
  (('y = 'y in set) & tree_ind{'y; t, f, g. "exists"{'t; a. 'f 'a = 'x in set}})
rewrite unfold_collect : collect{'T; x. 'a['x]} <--> tree{'T; lambda{x. 'a['x]}}

val fold_small_type : conv
val fold_set : conv
val fold_isset : conv
val fold_member : conv
val fold_collect : conv

(************************************************************************
 * SMALL TYPE RULES                                                     *
 ************************************************************************)

(*
(*
 * These are the types in the small universe.
 *)
axiom hyp_small 'H 'J :
   sequent ['ext] { 'H; a: small; 'J['a] >- small_type{'a} }

axiom int_small 'H :
   sequent ['ext] { 'H >- small_type{int} }

axiom fun_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H; a: 'A >- small_type{'B['a]} } -->
   sequent ['ext] { 'H >- small_type{(a: 'A -> 'B['a])} }

axiom exists_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H; a: 'A >- small_type{'B['a]} } -->
   sequent ['ext] { 'H >- small_type{(a: 'A * 'B['a])} }

axiom union_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- small_type{'B} } -->
   sequent ['ext] { 'H >- small_type{('A + 'B)} }

axiom equal_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'b = 'b in 'A } -->
   sequent ['ext] { 'H >- small_type{('a = 'b in 'A)} }

(*
 * There are no other small types.
 *)
axiom small_elim 'H 'J (a1: 'A1 -> 'B1) (a2:'A2 * 'B2) ('A3 + 'B3) ('a4 = 'b4 in 'A4) :
   sequent ['ext] { 'H; 'J[int] >- 'C[int] } -->
   sequent ['ext] { 'H; A1: small; B1: 'A1 -> small; 'J[(a1:'A1 -> 'B1 'a1)] >- 'C[(a1:'A1 -> 'B1 'a1)] } -->
   sequent ['ext] { 'H; A2: small; B2: 'A2 -> small; 'J[(a2:'A2 * 'B2 'a2)] >- 'C[(a2:'A2 * 'B2 'a2)] } -->
   sequent ['ext] { 'H; A3: small; B3: small; 'J[('A3 + 'B3)] >- 'C[('A3 + 'B3)] } -->
   sequent ['ext] { 'H; A4: small; a4: 'A4; b: 'A4; 'J[('a4 = 'b4 in 'A4)] >- 'C[('a4 = 'b4 in 'A4)] } -->
   sequent ['ext] { 'H; x: small; 'J['x] >- 'C['x] }
*)

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

(*
 * Equality from membership.
 *)
axiom equal_member 'H :
   sequent ['ext] { 'H >- member{'x; 's} } -->
   sequent ['ext] { 'H >- 'x = 'x in 's }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Set membership.
type memd_data

resource (term * tactic, tactic, memd_data) memd_resource

val memdT : tactic
 *)

(*
 * wf{'T} => type{'T}
 *)
val wf_typeT : tactic

(*
 * isset{'s} => 's = 's in set
 *)
val eqSetT : tactic

(*
 * member{'x; 's} => 'x = 'x in 's
 *)
val eqMemberT : tactic

(*
 * H, x: set, J >- isset{x}
 *)
val assumSetT : int -> tactic

(*
 * $Log$
 * Revision 1.4  1998/07/02 18:37:15  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.3  1998/06/23 22:12:25  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 * Revision 1.2  1998/06/16 16:26:05  jyh
 * Added itt_test.
 *
 * Revision 1.1  1998/06/15 22:32:50  jyh
 * Added CZF.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
