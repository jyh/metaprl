(*
 * Boolean operations.
 *)

include Itt_equal

open Resource

open Itt_equal

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "bool"
declare "btrue"
declare "bfalse"

declare ifthenelse{'e1; 'e2; 'e3}

(*
 * This term is used to reduce param actions.
 *)
declare "bool_flag"[@n:t]

primrw boolTrue : "bool_flag"["true":t] <--> "btrue"
primrw boolFalse : "bool_flag"["false":t] <--> "bfalse"

(*
 * Ifthenelse primrws.
 *)
primrw ifthenelseTrue : ifthenelse{btrue; 'e1; 'e2} <--> 'e1
primrw ifthenelseFalse : ifthenelse{bfalse; 'e1; 'e2} <--> 'e2

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Unit
 * by boolFormation
 *)
prim boolFormation 'H : : sequent ['ext] { 'H >- univ[@i:l] } =
   "bool"

(*
 * H >- Bool = Bool in Ui ext Ax
 * by boolEquality
 *)
prim boolEquality 'H : : sequent ['ext] { 'H >- "bool" = "bool" in univ[@i:l] } =
   "it"

(*
 * H >- Bool ext btrue
 * by bool_*Formation
 *)
prim bool_trueFormation 'H : : sequent ['ext] { 'H >- "bool" } =
   btrue

prim bool_falseFormation 'H : : sequent ['ext] { 'H >- "bool" } =
   bfalse

(*
 * H >- Unit = Unit in Ui ext Ax
 * by boolEquality
 *)
prim bool_trueEquality 'H : : sequent ['ext] { 'H >- btrue = btrue in "bool" } =
   "it"

prim bool_falseEquality 'H : : sequent ['ext] { 'H >- bfalse = bfalse in "bool" } =
   "it"

(*
 * H; i:x:Unit; J >- C
 * by boolElimination i
 * H; i:x:Unit; J[it / x] >- C[it / x]
 *)
prim boolElimination 'H 'J :
   ('btrue : sequent['ext] { 'H; x: "bool"; 'J[btrue] >- 'C[btrue] }) -->
   ('bfalse : sequent['ext] { 'H; x: "bool"; 'J[bfalse] >- 'C[bfalse] }) -->
   sequent ['ext] { 'H; x: "bool"; 'J['x] >- 'C['x] } =
   ifthenelse{'x; 'btrue; 'bfalse}

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Standard term.
 *)
let bool_term = << "bool" >>
let btrue_term = << btrue >>
let bfalse_term = << bfalse >>

(*
 * D
 *)
let d_boolT i p =
   let count = Sequent.hyp_count p in
      (if i = 0 then
          bool_trueFormation count
       else
          let i, j = Sequent.hyp_indices p i in
             boolElimination i j) p

let d_resource = d_resource.resource_improve d_resource (bool_term, d_boolT)

(*
 * EqCD.
 *)
let eqcd_boolT p =
   let count = Sequent.hyp_count p in
      boolEquality count p

let eqcd_btrueT p =
   let count = Sequent.hyp_count p in
      bool_trueEquality count p

let eqcd_bfalseT p =
   let count = Sequent.hyp_count p in
      bool_falseEquality count p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (bool_term, eqcd_boolT)
let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (btrue_term, eqcd_btrueT)
let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (bfalse_term, eqcd_bfalseT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of unit.
 *)
let inf_bool _ decl _ = decl, univ1_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (bool_term, inf_bool)

(*
 * Type of an equality is the type of the equality type.
 *)
let inf_btrue _ decl _ = decl, bool_term
let inf_bfalse _ decl _ = decl, bool_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (btrue_term, inf_btrue)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (bfalse_term, inf_bfalse)

(*
 * $Log$
 * Revision 1.1  1998/06/12 13:47:21  jyh
 * D tactic works, added itt_bool.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
