(*
 * Regular logic connectives.
 *
 *)

open Debug
open Resource

include Itt_equal
include Itt_dprod
include Itt_union
include Itt_void
include Itt_soft

(* debug_string DebugLoad "Loading itt_logic..." *)

(************************************************************************
 * REWRITES								*
 ************************************************************************)

declare "not"{'a}
declare "implies"{'a; 'b}
declare "and"{'a; 'b}
declare "or"{'a; 'b}
declare "all"{'A; x. 'B['x]}
declare "exists"{'A; x. 'B['x]}

primrw reduceNot : not{'a} <--> 'a -> void
primrw reduceImplies : 'a => 'b <--> 'a -> 'b
primrw reduceAnd : 'a & 'b <--> 'a * 'b
primrw reduceOr : 'a or 'b <--> 'a + 'b
primrw reduceAll : all x: 'A. 'B['x] <--> x:'A -> 'B['x]
primrw reduceExists : exists x: 'A. 'B['x] <--> x:'A * 'B['x]

(************************************************************************
 * DISPLAY FORMS							*
 ************************************************************************)

prec prec_implies
prec prec_and
prec prec_or
prec prec_quant

dform mode[src] :: parens :: "prec"[prec_implies] :: "not"{'a} =
   `"not " slot[le]{'a}

dform mode[src] :: parens :: "prec"[prec_implies] :: implies{'a; 'b} =
   slot[le]{'a} `" => " slot[lt]{'b}
   
dform mode[src] :: parens :: "prec"[prec_and] :: "and"{'a; 'b} =
   slot[le]{'a} `" /\\ " slot[lt]{'b}
   
dform mode[src] :: parens :: "prec"[prec_or] :: "or"{'a; 'b} =
   slot[le]{'a} `" \\/ " slot[lt]{'b}
   
dform mode[src] :: parens :: "prec"[prec_quant] :: "all"{'A; x. 'B['x]} =
   `"all " slot{'x} `": " slot{'A}`"." slot{'B['x]}

dform mode[src] :: parens :: "prec"[prec_quant] :: "exists"{'A; x. 'B['x]} =
  `"exists " slot{'x} `": " slot{'A} `"." slot{'B['x]}

dform mode[prl] :: parens :: "prec"[prec_implies] :: "not"{'a} =
   Nuprl_font!tneg slot[le]{'a}
   
dform mode[prl] :: parens :: "prec"[prec_implies] :: implies{'a; 'b} =
   slot[le]{'a} Nuprl_font!Rightarrow " " slot[lt]{'b}
   
dform mode[prl] :: parens :: "prec"[prec_and] :: "and"{'a; 'b} =
   slot[le]{'a} Nuprl_font!wedge " " slot[lt]{'b}
   
dform mode[prl] :: parens :: "prec"[prec_or] :: "or"{'a; 'b} =
   slot[le]{'a} Nuprl_font!vee " " slot[lt]{'b}
   
dform mode[prl] :: parens :: "prec"[prec_quant] :: "all"{'A; x. 'B['x]} =
   pushm[3] Nuprl_font!forall slot{'x} `":" slot{'A} sbreak["",". "] slot{'B['x]} popm

dform mode[prl] :: parens :: "prec"[prec_quant] :: "exists"{'A; x. 'B['x]} =
   pushm[3] Nuprl_font!"exists" slot{'x} `":" slot{'A} sbreak["",". "] slot{'B['x]}

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)
     
(*
 * D
 *)
let terms =
   [<< all x: 'A. 'B['x] >>,    reduceAll;
    << exists x: 'A. 'B['x] >>, reduceExists;
    << 'A or 'B >>,             reduceOr;
    << 'A & 'B >>,              reduceAnd;
    << 'A => 'B >>,             reduceImplies;
    << not 'A >>,               reduceNot]

let add arg =
   let rec aux (dr, er) = function
      (t, rw)::tl ->
         aux (add_soft_abs dr er t rw) tl
    | [] ->
         (dr, er)
   in
      aux arg

let d_resource, eqcd_resource = add (d_resource, eqcd_resource) terms
let d = d_resource.resource_extract d_resource
let eqcd = eqcd_resource.resource_extract eqcd_resource

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:52:17  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.4  1996/10/23 15:18:09  jyh
 * First working version of dT tactic.
 *
 * Revision 1.3  1996/09/25 22:52:13  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.2  1996/09/02 19:37:30  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.1  1996/06/11 18:38:38  jyh
 * Demo version 0.0
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
