(*
 * Empty set.
 *)

include Czf_itt_set

open Refiner.Refiner.RefineError
open Resource

open Sequent
open Tacticals

open Itt_logic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "union"{'s1; 's2}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_union : union{'s1; 's2} <-->
   set_ind{'s1; a1, f1, g1.
      set_ind{'s2; a2, f2, g2.
         collect{.Itt_union!union{'a1; 'a2}; x. decide{'x; z. 'f1 'z; z. 'f2 'z}}}}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform union_df : mode[prl] :: parens :: "prec"[prec_or] :: union{'s1; 's2} =
   slot{'s1} " " cup " " slot{'s2}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Union is a set.
 *)
interactive union_isset 'H :
   sequent ['ext] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- isset{union{'s1; 's2}} }

(*
 * Membership in a union.
 *)
interactive union_member_intro_left 'H :
   sequent ['ext] { 'H >- member{'x; 's1} } -->
   sequent ['ext] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- member{'x; union{'s1; 's2}} }

interactive union_member_intro_right 'H :
   sequent ['ext] { 'H >- member{'x; 's2} } -->
   sequent ['ext] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- member{'x; union{'s1; 's2}} }

(*
 * Nothing is in the empty set.
 *)
interactive union_member_elim 'H 'J :
   sequent ['ext] { 'H; x: member{'y; 's1}; 'J['x] >- 'T['x] } -->
   sequent ['ext] { 'H; x: member{'y; 's2}; 'J['x] >- 'T['x] } -->
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x] >- 'T['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Sethood.
 *)
let d_union_setT i p =
   if i = 0 then
      union_isset (hyp_count p) p
   else
      raise (RefineError ("d_union_issetT", StringError "no elimination form"))

let union_isset_term = << isset{union{'s1; 's2}} >>

let d_resource = d_resource.resource_improve d_resource (union_isset_term, d_union_setT)

(*
 * Membership.
 *)
let d_unionT i p =
   if i = 0 then
      try
         let j = get_sel_arg p in
         let rule =
            if j = 0 then
               union_member_intro_left
            else
               union_member_intro_right
         in
            rule (hyp_count p) p
      with
         RefineError _ ->
            raise (RefineError ("d_unionT", StringError "d_unionT requires a selT argument"))
   else
      let i, j = hyp_indices p i in
         union_member_elim i j p

let union_member_term = << member{'x; union{'s1; 's2}} >>

let d_resource = d_resource.resource_improve d_resource (union_member_term, d_unionT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
