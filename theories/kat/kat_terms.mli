extends Base_theory
extends Support_algebra
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

declare kleene

declare le{'x; 'y}

declare ge{'x; 'y}
