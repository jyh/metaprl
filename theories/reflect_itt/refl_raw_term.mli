(*
 * Definition of terms.
 *)

include Itt_theory

include Refl_var

open Refiner.Refiner.TermType

open Conversionals
open Tacticals

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Parts of terms.
 *)
declare operator_type
declare eq_op{'op1; 'op2}

declare bterm{'sl; 't}
declare bterm_term{'bt}
declare raw_bterm_type{'T}

declare bvar{'v; 'terms}
declare bvar_type{'T}

declare term{'op; 'bterms}
declare raw_term_type

declare match_term{'t; v, tl. 'bvar_case['v; 'tl]; op, bterms. 'term_case['op; 'bterms]}
declare match_bterm{'bterm; sl, t. 'body['sl; 't]}

prec prec_eq_op

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

topval unfold_bterm : conv
topval unfold_bterm_term : conv
topval unfold_raw_bterm_type : conv
topval unfold_bvar : conv
topval unfold_bvar_type : conv
topval unfold_term : conv
topval unfold_raw_term_type : conv
topval unfold_match_term : conv

topval fold_bterm : conv
topval fold_bterm_term : conv
topval fold_raw_bterm_type : conv
topval fold_bvar : conv
topval fold_bvar_type : conv
topval fold_term : conv
topval fold_raw_term_type : conv
topval fold_match_term : conv

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval eq_opRefT : tactic
topval eq_opSymT : tactic
topval eq_opTransT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
