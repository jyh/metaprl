doc <:doc< 
   @begin[doc]
   @module[Czf_itt_setdiff]
   @parents
   @end[doc]
>>
extends Czf_itt_set
extends Czf_itt_member
extends Czf_itt_empty
extends Czf_itt_nat
extends Czf_itt_sep
extends Itt_bool

doc <:doc< @docoff >>

open Lm_debug

open Tactic_type.Conversionals

open Dtactic

let _ =
   show_loading "Loading Czf_itt_setdiff%t"

doc <:doc< @doc{@terms} >>
declare setdiff{'s1; 's2}

doc <:doc< 
   @begin[doc]
   @rewrites
  
   @tt[setdiff] is defined using restricted separation.
   @end[doc]
>>
prim_rw unfold_setdiff : setdiff{'s1; 's2} <-->
   sep{'s1; x. "implies"{mem{'x; 's2}; ."false"}}
(*   set_ind{'s1; T1, f1, g1.
         collect{'T1; x. ifthenelse{mem{.'f1 'x; 's2}; empty; .'f1 'x}}} *)

doc <:doc< @docoff >>
let fold_setdiff = makeFoldC << setdiff{'s1; 's2} >> unfold_setdiff

prec prec_setdiff

dform setdiff_df : except_mode[src] :: parens :: "prec"[prec_setdiff] :: setdiff{'s1; 's2} =
   slot{'s1} `" - " slot{'s2}

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Well-formedness}
  
   A @tt[setdiff] is well-formed if its arguments are both sets.
   @end[doc]
>>
interactive setdiff_isset {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- isset{setdiff{'s1; 's2}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction}
  
   A set $x$ is in the difference set @setdiff{s1; s2} if $x$ is a
   member of $s_1$ and $x$ is not a member of $s_2$.
   @end[doc]
>>
interactive setdiff_intro {| intro [] |} 'x :
   ["wf"] sequent { <H> >- isset{'x} } -->
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'x; 's1} } -->
   sequent { <H> >- "implies"{mem{'x; 's2}; ."false"} } -->
   sequent { <H> >- mem{'x; setdiff{'s1; 's2}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Elimination}
  
   The elimination form of @setdiff{s_1; s_2} produces a proof that
   $@mem{x; s_2}$ is wrong for which $@mem{x; s_1}$.
   @end[doc]
>>
interactive setdiff_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: mem{'y; setdiff{'s1; 's2}}; <J['x]> >- isset{'y} } -->
   ["wf"] sequent { <H>; x: mem{'y; setdiff{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: mem{'y; setdiff{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
   sequent { <H>; x: mem{'y; setdiff{'s1; 's2}}; <J['x]>; u: mem{'y; 's1}; v: "implies"{mem{'y; 's2}; ."false"} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; setdiff{'s1; 's2}}; <J['x]> >- 'T['x] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Functionality}
  
   A @tt[setdiff] type is functional in both set arguments.
   @end[doc]
>>
interactive setdiff_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's1['z]} } -->
   sequent { <H> >- fun_set{z. 's2['z]} } -->
   sequent { <H> >- fun_set{z. setdiff{'s1['z]; 's2['z]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)

(* interactive setdiff1 :
   sequent { <H> >- eq{setdiff{succ{empty}; empty}; succ{empty}} }

interactive setdiff2 :
   sequent { <H> >- eq{setdiff{succ{empty}; succ{empty}}; empty} }
*)
