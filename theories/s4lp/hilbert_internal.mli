open Lm_symbol

module LP :
sig
   type proof_term =
      Var of symbol
    | Const of int
    | App of proof_term * proof_term
    | Plus of proof_term * proof_term
    | Check of proof_term
    | Provisional of int
    | PropTaut of formula

   and agent = Modal of int | Evidence of int

   and formula =
      Falsum
    | Atom of symbol
    | And of formula * formula
    | Or of formula * formula
    | Neg of formula
    | Implies of formula * formula
    | Box of agent * formula
    | Pr of proof_term * formula

   type 'formula hilbert =
      Axiom of int
    | MP of 'formula * 'formula hilbert * 'formula hilbert
    | Choice of 'formula hilbert * 'formula hilbert
    | Hyp of int
	 | ConstSpec
	 | Nec of int * 'formula hilbert

	val weaker_or_equal : formula -> formula -> bool

end

open LP

module OrderedFormula :
sig
	type t = formula

	val fam_cmp : agent -> agent -> int
	val compare_pterm : proof_term -> proof_term -> int
	val compare : formula -> formula -> int
	val compare_pairs : formula * formula -> formula * formula -> int
end

module FSet : Lm_set_sig.LmSetDebug with type elt = OrderedFormula.t

module S4G :
sig
   type fset = FSet.t

   type rule_node =
      Axiom of LP.formula
    | AxiomFalsum
    | NegLeft of LP.formula * gentzen
    | ImplLeft of LP.formula * LP.formula * gentzen * gentzen
    | ImplRight of LP.formula * LP.formula * gentzen
	 | AndLeft of LP.formula * LP.formula * gentzen
	 | AndRight of LP.formula * LP.formula * gentzen * gentzen
	 | OrLeft of LP.formula * LP.formula * gentzen * gentzen
    | BoxRight of int * LP.formula * gentzen
    | BoxLeft of LP.formula * gentzen

   and gentzen = rule_node * fset * fset (* rule, hyps, concls *)
end

val check_proof : formula list -> formula hilbert -> formula -> bool
val lift : formula list -> formula hilbert -> formula -> formula hilbert * proof_term
val deduction : formula -> formula list -> formula hilbert -> formula -> formula hilbert
val realize : S4G.gentzen -> proof_term * formula * formula hilbert
