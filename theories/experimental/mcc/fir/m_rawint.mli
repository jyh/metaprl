extends Base_theory

(*
 * For now, use the string representation.
 *)
declare rawint[precision:n, signed:t, value:s]

(*
 * Arithmetic.
 *)
declare rawint_uminus{'i}
declare rawint_lnot{'i}
declare rawint_bitfield[off:n, len:n]{'i}

declare rawint_of_rawint[p:n, s:t]{'i}
declare rawint_of_int[p:n, s:t]{'i}

declare rawint_plus{'i1; 'i2}
declare rawint_minus{'i1; 'i2}
declare rawint_mul{'i1; 'i2}
declare rawint_div{'i1; 'i2}
declare rawint_rem{'i1; 'i2}
declare rawint_max{'i1; 'i2}
declare rawint_min{'i1; 'i2}

declare rawint_sl{'i1; 'i2}
declare rawint_sr{'i1; 'i2}
declare rawint_and{'i1; 'i2}
declare rawint_or{'i1; 'i2}
declare rawint_xor{'i1; 'i2}

declare rawint_if_eq{'i1; 'i2; 'e1; 'e2}
declare rawint_if_lt{'i1; 'i2; 'e1; 'e2}

(*
 * Precedences.
 *)
prec prec_shift
prec prec_and
prec prec_add
prec prec_mul
prec prec_uminus
prec prec_apply

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
