(*
 * Definition of terms.
 *)

include Itt_theory

open Conversionals

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Parts of terms.
 *)
declare opname{'l}
declare opname_eq{'op1; 'op2}
declare opname_type

declare level{'i; 'levels}
declare level_type

declare "pstring"{'s}
declare "ptoken"{'t}
declare "pvar"{'v}
declare "pint"{'i}
declare "plevel"{'l}
declare "mstring"{'s}
declare "mtoken"{'s}
declare "mvar"{'s}
declare "mint"{'s}
declare "mlevel"{'s}
declare param_type

declare operator{'name; 'params}
declare operator_type

declare bterm{'sl; 't}
declare bterm_type{'t}

declare term{'op; 'bterms}
declare term_type

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_level : level{'i; 'levels} <--> pair{'i; 'levels}
rewrite unfold_level_type : level_type <--> (int * list{.atom * int})

rewrite unfold_param : param_type <-->
   (atom        (* string *)
    + atom      (* token *)
    + atom      (* var *)
    + int       (* int *)
    + level     (* level *)
    + atom      (* mstring *)
    + atom      (* mtoken *)
    + atom      (* mvar *)
    + atom      (* mint *)
    + atom      (* mlevel *)
    + void)
rewrite unfold_pstring : pstring{'s} <--> inl{'s}
rewrite unfold_ptoken  : ptoken{'t}  <--> inr{inl{'t}}
rewrite unfold_pvar    : pvar{'v}    <--> inr{inr{inl{'v}}}
rewrite unfold_pint    : pint{'i}    <--> inr{inr{inr{inl{'i}}}}
rewrite unfold_plevel  : plevel{'l}  <--> inr{inr{inr{inr{inl{'l}}}}}
rewrite unfold_mstring : mstring{'s} <--> inr{inr{inr{inr{inr{inl{'s}}}}}}
rewrite unfold_mtoken  : mtoken{'s}  <--> inr{inr{inr{inr{inr{inr{inl{'s}}}}}}}
rewrite unfold_mvar    : mvar{'s}    <--> inr{inr{inr{inr{inr{inr{inr{inl{'s}}}}}}}}
rewrite unfold_mint    : mint{'s}    <--> inr{inr{inr{inr{inr{inr{inr{inr{inl{'s}}}}}}}}}
rewrite unfold_mlevel  : mlevel{'s}  <--> inr{inr{inr{inr{inr{inr{inr{inr{inr{inl{'s}}}}}}}}}}

rewrite unfold_operator : operator{'name; 'params} <--> pair{'name; 'params}
rewrite unfold_operator_type : operator_type <--> (opname_type * param_type list)

rewrite unfold_bterm : bterm{'sl; 't} <--> pair{'sl, 't}
rewrite unfold_bterm_type : bterm_type{'T} <--> (list{atom} * 'T)

rewrite unfold_term : term{'op; 'bterms} <--> pair{'op; 'bterms}
rewrite unfold_term_type : term_type <--> srec{T. operator_type * list{bterm_type{'T}}}

val fold_level : conv
val fold_level_type : conv

val fold_param : conv
val fold_pstring : conv
val fold_ptoken : conv
val fold_pvar : conv
val fold_pint : conv
val fold_plevel : conv
val fold_mstring : conv
val fold_mtoken : conv
val fold_mvar : conv
val fold_mint : conv
val fold_mlevel : conv

val fold_operator : conv
val fold_operator_type : conv

val fold_bterm : conv
val fold_bterm_type : conv

val fold_term : conv
val fold_term_type : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
