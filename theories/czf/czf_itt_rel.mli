(*
 * Assert a relation between two sets.
 *)

include Czf_itt_dall
include Czf_itt_dexists

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Relation P holds between the two sets.
 *)
declare rel{a, b. 'P['a; 'b]; 's1; 's2}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_rel : rel{a, b. 'P['a; 'b]; 's1; 's2} <-->
   (dall{'s1; x. dexists{'s2; y. 'P['x; 'y]}} & dall{'s2; y. dexists{'s1; x. 'P['x; 'y]}})

(*
 * $Log$
 * Revision 1.1  1998/07/17 15:39:09  jyh
 * CZF is complete, although we may wish to add pairing and inf.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
