extends Perv

open Basic_tactics

declare rnil
declare rcons{'hd; 'tl}

declare shape[op:op]

(*
 * Primitive lists.
 *)
val is_rnil_term : term -> bool
val rnil_term : term

val is_rcons_term : term -> bool
val mk_rcons_term : term -> term -> term
val dest_rcons : term -> term * term

val is_rlist_term : term -> bool
val dest_rlist : term -> term list
val mk_rlist_term : term list -> term

topval reduce_shape : conv
