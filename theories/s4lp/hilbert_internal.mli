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

   and family = Modal of int | Evidence of int

   and formula =
      Falsum
    | Atom of symbol
    | And of formula * formula
    | Or of formula * formula
    | Neg of formula
    | Implies of formula * formula
    | Box of family * formula
    | Pr of proof_term * formula

   type 'formula hilbert =
      Axiom of int
    | MP of 'formula * 'formula hilbert * 'formula hilbert
    | Choice of 'formula hilbert * 'formula hilbert
    | Hyp of int
	 | ConstSpec

end

open LP

module OrderedFormula :
sig
	type t = formula

	val fam_cmp : family -> family -> int
	val compare_pterm : proof_term -> proof_term -> int
	val compare : formula -> formula -> int
	val compare_pairs : formula * formula -> formula * formula -> int
end

module FSet : Lm_set_sig.LmSet with type elt = OrderedFormula.t

val check_proof : formula list -> formula hilbert -> formula -> bool
val lift : formula list -> formula hilbert -> formula -> formula hilbert * proof_term
val deduction : formula -> formula list -> formula hilbert -> formula -> formula hilbert

