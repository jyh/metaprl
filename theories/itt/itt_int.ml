(*
 * Int is the type of tokens (strings)
 *
 *)

include Tactic_type

include Itt_equal
include Itt_rfun
include Itt_bool
include Itt_logic

open Printf
open Debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.Refine
open Rformat
open Resource

open Var
open Sequent
open Tacticals
open Itt_equal

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_int%t" eflush

(* debug_string DebugLoad "Loading itt_int..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare int
declare natural_number[@n:n]
declare ind{'i; m, z. 'down; 'base; m, z. 'up}

declare "add"{'a; 'b}
declare "sub"{'a; 'b}
declare "mul"{'a; 'b}
declare "div"{'a; 'b}
declare "rem"{'a; 'b}
declare lt{'a; 'b}
declare le{'a; 'b}
declare ge{'a; 'b}
declare gt{'a; 'b}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_compare
prec prec_add
prec prec_mul

(*
prec prec_mul < prec_apply
prec prec_add < prec_mul
prec prec_compare < prec_add
*)

dform int_prl_df1 : mode[prl] :: int = mathbbZ

mldform natural_number_df : natural_number[@n:n] print_term buf =
   format_int buf n

dform add_df1 :  mode[prl] :: parens :: "prec"[prec_add] :: "add"{'a; 'b} =
   slot[le]{'a} `" + " slot[lt]{'b}
dform add_df2 : mode[src] :: parens :: "prec"[prec_add] :: "add"{'a; 'b} =
   slot[le]{'a} `" add " slot[lt]{'b}

dform sub_df1 : mode[prl] :: parens :: "prec"[prec_add] :: "sub"{'a; 'b} =
   slot[lt]{'a} `" - " slot[le]{'b}
dform sub_df2 : mode[src] :: parens :: "prec"[prec_add] :: "sub"{'a; 'b} =
   slot[lt]{'a} `" sub " slot[le]{'b}

dform mul_df1 : mode[prl] :: parens :: "prec"[prec_mul] :: "mul"{'a; 'b} =
   slot[lt]{'a} `" * " slot[le]{'b}
dform mul_df2 : mode[src] :: parens :: "prec"[prec_mul] :: "mul"{'a; 'b} =
   slot[lt]{'a} `" mul " slot[le]{'b}

dform div_df1 : mode[prl] :: parens :: "prec"[prec_mul] :: "div"{'a; 'b} =
   slot[lt]{'a} Nuprl_font!"div" slot[le]{'b}
dform div_df2 : mode[src] :: parens :: "prec"[prec_mul] :: "div"{'a; 'b} =
   slot[lt]{'a} `" div " slot[le]{'b}

dform rem_df1 : mode[prl] :: parens :: "prec"[prec_mul] :: "rem"{'a; 'b} =
   slot[lt]{'a} `" % " slot[le]{'b}
dform rem_df2 : mode[src] :: parens :: "prec"[prec_mul] :: "rem"{'a; 'b} =
   slot[lt]{'a} `" rem " slot[le]{'b}

dform lt_df1 : parens :: "prec"[prec_compare] :: lt{'a; 'b} =
   slot[lt]{'a} `" < " slot[le]{'b}

dform le_df1 : mode[prl] :: parens :: "prec"[prec_compare] :: le{'a; 'b} =
   slot[lt]{'a} Nuprl_font!le slot[le]{'b}
dform le_df2 : mode[src] :: parens :: "prec"[prec_compare] :: le{'a; 'b} =
   slot[lt]{'a} `" <= " slot[le]{'b}

dform ge_df1 : mode[prl] :: parens :: "prec"[prec_compare] :: ge{'a; 'b} =
   slot[lt]{'a} Nuprl_font!ge slot[le]{'b}
dform ge_df2 : mode[src] :: parens :: "prec"[prec_compare] :: ge{'a; 'b} =
   slot[lt]{'a} `" >= " slot[le]{'b}

dform gt_df1 : parens :: "prec"[prec_compare] :: gt{'a; 'b} =
   slot[lt]{'a} `" > " slot[le]{'b}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw reduceLE : le{'a; 'b} <--> ('a < 'b or 'a = 'b in int)
primrw reduceGT : gt{'a; 'b} <--> 'b < 'a
primrw reduceGE : ge{'a; 'b} <--> ('b < 'a or 'a = 'b in int)

primrw reduceAdd : "add"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i + @j]
primrw reduceSub : "sub"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i - @j]
primrw reduceMul : "mul"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i * @j]
primrw reduceDiv : "div"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i / @j]
primrw reduceRem : "rem"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i % @j]
primrw reduceLT  : "lt"{natural_number[@i:n]; natural_number[@j:n]}  <--> bool_flag[@i < @j]

(*
 * Reduction on induction combinator:
 * Three cases:
 *    let ind[x] = ind(x; i, j. down[i, j]; base; k, l. up[k, l]
 *    x < 0 => (ind[x] -> down[x, ind[x + 1]]
 *    x = 0 => (ind[x] -> base)
 *    x > 0 => (ind[x] -> up[x, ind[x - 1]]
 *)
primrw indReduceDown :
   'x < 0 -->
   ((ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) <-->
    'down['x; ind{('x +@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

primrw indReduceUp :
   ('x > 0) -->
   (ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
    'up['x; ind{('x -@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

primrw indReduceBase :
   (ind{0; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) <-->
   'base

mlterm indReduce{ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}} =
   raise (RefineError ("indReduce", StringError "not implemented"))
 | fun _ _ ->
      raise (RefineError ("indReduce", StringError "not implemented"))

primrw indReduce : ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
   indReduce{ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Reduction on induction combinator:
 * Three cases:
 *    let ind[x] = ind(x; i, j. down[i, j]; base; k, l. up[k, l]
 *    x < 0 => (ind[x] -> down[x, ind[x + 1]]
 *    x = 0 => (ind[x] -> base)
 *    x > 0 => (ind[x] -> up[x, ind[x - 1]]
 *)
(*
rwthm indReduce ind('x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]) =
   let n = dest_natural_number x in
      if n > 0 then
         << 'down['x; 'redex] >>
      else if n < 0 then
         << 'up['x; 'redex] >>
      else
         << 'base >>
   mlend
*)

(************************************************************************
 * INTEGER RULES                                                        *
 ************************************************************************)

(*
 * H >- Ui ext Z
 * by intFormation
 *)
prim intFormation 'H : : sequent ['ext] { 'H >- univ[@i:l] } = int

(*
 * H >- Z = Z in Ui ext Ax
 * by intEquality
 *)
prim intEquality 'H : : sequent ['ext] { 'H >- int = int in univ[@i:l] } = it

(*
 * H >- Z ext n
 * by numberFormation n
 *)
prim numberFormation 'H natural_number[@n:n] : : sequent ['ext] { 'H >- int } = natural_number[@n:n]

(*
 * Induction:
 * H, n:Z, J[n] >- C[n] ext ind(n; m, z. down[n, m, it, z]; base[n]; m, z. up[n, m, it, z])
 * by intElimination [m; v; z]
 *
 * H, n:Z, J[n], m:Z, v: m < 0, z: C[m + 1] >- C[m] ext down[n, m, v, z]
 * H, n:Z, J[n] >- C[0] ext base[n]
 * H, n:Z, J[n], m:Z, v: 0 < m, z: C[m - 1] >- C[m] ext up[n, m, v, z]
 *)
prim intElimination 'H 'J 'n 'm 'v 'z :
   ('down['n; 'm; 'v; 'z] : sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 'm < 0; z: 'C['m add 1] >- 'C['m] }) -->
   ('base['n] : sequent ['ext] { 'H; n: int; 'J['n] >- 'C[0] }) -->
   ('up['n; 'm; 'v; 'z] : sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 0 < 'm; z: 'C['m sub 1] >- 'C['m] }) -->
   sequent ['ext] { 'H; n: int; 'J['n] >- 'C['n] } =
   ind{'n; m, z. 'down['n; 'm; it; 'z]; 'base['n]; m, z. 'up['n; 'm; it; 'z]}

(*
 * Equality on induction combinator:
 * let a = ind(x1; i1, j1. down1[i1, j1]; base1; k1, l1. up1[k1, l1])
 * let b = ind(x2; i2, j2. down2[i2, j2]; base2; k2, l2. up2[k2, l2])
 *
 * H >- a = b in T[x1]
 * by indEquality [z. T[z]; x; y; w]
 *
 * H >- x1 = y1 in Z
 * H, x: Z, w: x < 0, y: T[x + 1] >- down1[x, y] = down2[x, y] in T[x]
 * H >- base1 = base2 in T[0]
 * H, x: Z, w: 0 < x, y: T[x - 1] >- up1[x, y] = up2[x, y] in T[x]
 *)
prim indEquality 'H lambda{z. 'T['z]} 'x 'y 'w :
   sequent [squash] { 'H >- 'x1 = 'x2 in int } -->
   sequent [squash] { 'H; x: int; w: 'x < 0; y: 'T['x add 1] >- 'down1['x; 'y] = 'down2['x; 'y] in 'T['x] } -->
   sequent [squash] { 'H >- 'base1 = 'base2 in 'T[0] } -->
   sequent [squash] { 'H; x: int; w: 'x > 0; y: 'T['x sub 1] >- 'up1['x; 'y] = 'up2['x; 'y] in 'T['x] } -->
   sequent ['ext] { 'H >- ind{'x1; i1, j1. 'down1['i1; 'j1]; 'base1; k1, l1. 'up1['k1; 'l1]}
                   = ind{'x2; i2, j2. 'down2['i2; 'j2]; 'base2; k2, l2. 'up2['k2; 'l2]}
                   in 'T['x1] } =
   it

(*
 * less_thanFormation:
 * H >- Ui ext a < b
 * by less_thanFormation
 *
 * H >- Z ext a
 * H >- Z ext b
 *)
prim less_thanFormation 'H :
   ('a : sequent ['ext] { 'H >- int }) -->
   ('b : sequent ['ext] { 'H >- int }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   'a < 'b

(*
 * H >- i1 < j1 = i2 < j2 in Ui
 * by less_thanEquality
 *
 * H >- i1 = j1 in int
 * H >- i2 = j2 in int
 *)
prim less_thanEquality 'H :
   sequent [squash] { 'H >- 'i1 = 'j1 in int } -->
   sequent [squash] { 'H >- 'i2 = 'j2 in int } -->
   sequent ['ext] { 'H >- 'i1 < 'j1 = 'i2 < 'j2 in univ[@i:l] } =
   it

(*
 * H >- it = it in (a < b)
 * by less_than_memberEquality
 *
 * H >- a < b
 *)
prim less_than_memberEquality 'H :
   sequent [squash] { 'H >- 'a < 'b } -->
   sequent ['ext] { 'H >- it = it in ('a < 'b) } =
   it

(*
 * H, x: a < b, J[x] >- C[x]
 * by less_than_Elimination i
 *
 * H, x: a < b; J[it] >- C[it]
 *)
prim less_thanElimination 'H 'J :
   ('t : sequent ['ext] { 'H; x: 'a < 'b; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: 'a < 'b; 'J['x] >- 'C['x] } =
   't

(************************************************************************
 * ARITH                                                                *
 ************************************************************************)

(*
 * H >- i = j in Z
 * by arith
 *
 * This is the large decision procedure.
 *)
mlterm arith_check{'t} =
   raise (RefineError ("arith", StringError "not implemented"))
 | fun _ _ ->
      raise (RefineError ("arith", StringError "not implemented"))

prim arith : arith_check{'t} --> 't = it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let int_term = << int >>

let natural_number_term = << natural_number[@n:n] >>
let natural_number_opname = opname_of_term natural_number_term
let is_natural_number_term = is_number_term natural_number_opname
let dest_natural_number = dest_number_term natural_number_opname
let mk_natural_number_term = mk_number_term natural_number_opname

let ind_term = << ind{'i; m, z. 'down; 'base; m, z. 'up} >>
let ind_opname = opname_of_term ind_term
let is_ind_term = is_dep0_dep2_dep0_dep2_term ind_opname
let dest_ind = dest_dep0_dep2_dep0_dep2_term ind_opname
let mk_ind_term = mk_dep0_dep2_dep0_dep2_term ind_opname

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D
 *)
let zero = << 0 >>

let d_intT i p =
   if i = 0 then
      numberFormation (hyp_count p) zero p
   else
      let i, j = hyp_indices p i in
      let n, _ = Sequent.nth_hyp p i in
         match maybe_new_vars ["m"; "v"; "z"] (Sequent.declared_vars p) with
            [m; v; z] ->
               intElimination i j n m v z p
          | _ ->
               failwith "d_int: match"

let d_resource = d_resource.resource_improve d_resource (int_term, d_intT)

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

(*
 * EqCD int.
 *)
let eqcd_intT p = intEquality (hyp_count p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (int_term, eqcd_intT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of int.
 *)
let inf_int _ decl _ = decl, univ1_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (int_term, inf_int)

(*
 * Type of natural_number.
 *)
let inf_natural_number _ decl _ = decl, int_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (natural_number_term, inf_natural_number)

(*
 * Type of ind.
 *)
let inf_ind inf decl t =
   let i, a, b, down, base, c, d, up = dest_ind t in
      inf decl base

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (ind_term, inf_ind)

(*
 * $Log$
 * Revision 1.10  1998/06/12 13:47:28  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.9  1998/06/09 20:52:36  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.8  1998/06/01 13:55:54  jyh
 * Proving twice one is two.
 *
 * Revision 1.7  1998/05/28 13:47:37  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.6  1998/04/24 02:43:30  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.5  1998/04/22 22:44:48  jyh
 * *** empty log message ***
 *
 * Revision 1.4  1998/04/21 20:58:07  jyh
 * Fixed typing problems introduced by refiner msequents.
 *
 * Revision 1.3  1998/04/09 18:26:05  jyh
 * Working compiler once again.
 *
 * Revision 1.2  1997/08/06 16:18:31  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:13  jyh
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
 * Revision 1.6  1996/10/23 15:18:07  jyh
 * First working version of dT tactic.
 *
 * Revision 1.5  1996/09/25 22:52:12  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.4  1996/05/21 02:16:49  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.3  1996/03/28 02:51:31  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.2  1996/03/05 19:59:45  jyh
 * Version just before LogicalFramework.
 *
 * Revision 1.1  1996/02/13 21:35:58  jyh
 * Intermediate checkin while matching is bing added to the refiner.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
