extends Perv

open Basic_tactics

declare rnil
declare rcons{'hd; 'tl}

declare sequent [bterm] { Term : Term >- Term } : Term
declare term

declare if_quoted_op{'op; 'tt}

declare if_bterm{'t; 'tt}
declare subterms{'bt}
declare make_bterm{'bt; 'bt1}
declare if_same_op{'bt1; 'bt2; 'tt; 'ff}
declare if_simple_bterm{'bt; 'tt; 'ff}
declare if_var_bterm{'bt; 'tt; 'ff}
declare subst{'bt; 't}

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

topval reduce_ifbterm : conv
topval reduce_if_var_bterm : conv
topval reduce_subterms : conv
topval reduce_make_bterm : conv
topval reduce_if_same_op : conv
topval reduce_if_simple_bterm : conv
topval reduce_subst : conv
