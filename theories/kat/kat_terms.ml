extends Base_theory
extends Base_select
extends Itt_struct2

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)


declare number[n:n] (* 1 and 0 *)

declare prod{'x;'y} (*   'x * 'y  *)

declare union{'x;'y} (*   'x + 'y  *)

declare minus{'x}    (*   ~'x  *)

declare star{'x}    (*   'x^*  *)

declare bool

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_star
prec prec_mul
prec prec_mul < prec_star
prec prec_neg
prec prec_neg < prec_mul
prec prec_add
prec prec_add < prec_neg

dform one_zero_df : number[n:n] =
   slot[n:n]

dform prod_df : parens :: "prec"[prec_mul] :: ('x * 'y) =
   slot["le"]{'x} " " slot["lt"]{'y}

dform plus_df : parens :: "prec"[prec_add] :: ('x + 'y) =
   slot["le"]{'x} `" + " slot["lt"]{'y}

dform negation_df : parens :: "prec"[prec_neg] :: (- 'a) =
   tneg slot["le"]{'a}

dform star_df : parens :: "prec"[prec_star] :: star{'a} =
   slot["le"]{'a} sup{slot["*"]}

dform bool_df : bool = mathbbB




