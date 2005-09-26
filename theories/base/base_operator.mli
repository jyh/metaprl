extends Perv

open Basic_tactics

declare rnil
declare rcons[hd:n]{'tl}

declare shape[op:op]

(*
 * Primitive lists.
 *)
val is_rnil_term : term -> bool
val rnil_term : term

val is_rcons_term : term -> bool
val mk_rcons_term : Lm_num.num -> term -> term
val dest_rcons : term -> Lm_num.num * term

val is_numlist_term : term -> bool
val dest_numlist : term -> Lm_num.num list
val mk_numlist_term : int list -> term

topval reduce_shape : conv
