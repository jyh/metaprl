extends Cic_ind_type

open Basic_tactics

declare case{'t;'P;'F}
declare sequent [cases] { Term : Term >- Term } : Term



topval gen : string -> term -> int -> int -> tactic
(*topval gen2 : tactic*)
