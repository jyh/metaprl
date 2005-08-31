extends Perv

open Basic_tactics

declare rnil
declare rcons{'hd; 'tl}

declare if_quoted_op{'op; 'tt}
declare shape{'op}
declare if_same_op{'bt1; 'bt2; 'tt; 'ff}

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

topval reduce_if_quoted_op : conv
topval reduce_if_same_op : conv
topval reduce_shape : conv
