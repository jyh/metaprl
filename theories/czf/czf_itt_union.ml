(*
 * Empty set.
 *)

include Czf_itt_member

open Printf
open Nl_debug

open Refiner.Refiner.RefineError
open Resource

open Sequent
open Tacticals
open Conversionals
open Var

open Itt_logic

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_union%t" eflush

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

interactive_rw reduce_union : union{collect{'t1; x1. 'f1['x1]};
                                    collect{'t2; x2. 'f2['x2]}} <-->
   collect{.Itt_union!union{'t1; 't2}; x. decide{'x; z. 'f1['z]; z. 'f2['z]}}

let fold_union = makeFoldC << union{'s1; 's2} >> unfold_union

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
 * We get a slightly less powerful elim form.
 *)
interactive union_member_elim3 'H 'J 'z :
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x] >- isset{'s1} } -->
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x] >- isset{'s2} } -->
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x]; z: member{'y; 's1} >- 'T['x] } -->
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x]; z: member{'y; 's2} >- 'T['x] } -->
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x] >- 'T['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Sethood.
 *)
let d_union_setT i p =
   if i = 0 then
      union_isset (hyp_count_addr p) p
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
            if j = 1 then
               union_member_intro_left
            else
               union_member_intro_right
         in
            rule (hyp_count_addr p) p
      with
         RefineError _ ->
            raise (RefineError ("d_unionT", StringError "d_unionT requires a selT argument"))
   else
      let i, j = hyp_indices p i in
      let z = maybe_new_vars1 p "z" in
         union_member_elim3 i j z p

let union_member_term = << member{'x; union{'s1; 's2}} >>

let d_resource = d_resource.resource_improve d_resource (union_member_term, d_unionT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
