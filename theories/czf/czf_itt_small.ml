(*
 * Small type is used to index the set w-type.
 * The small type is just U1.
 *)

include Itt_theory

open Printf
open Nl_debug

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Nl_resource

open Tacticals
open Conversionals
open Sequent
open Var

open Itt_equal

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_small%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * These are the small types from which sets are built.
 *    small: the type of small propositions
 *    small_type{'t}: 't = 't in small
 *)
declare small
declare small_type{'t}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_small : small <--> univ[1:l]
primrw unfold_small_type : small_type{'t} <--> ('t = 't in small)

let fold_small = makeFoldC << small >> unfold_small
let fold_small_type = makeFoldC << small_type{'t} >> unfold_small_type

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform small_df : small =
   `"small"

dform small_type_df : small_type{'t} =
   slot{'t} " " `"small_type"

(************************************************************************
 * SMALL TYPE RULES                                                     *
 ************************************************************************)

interactive small_type 'H : :
   sequent ['ext] { 'H >- "type"{small} }

interactive small_type_type 'H :
   sequent [squash] { 'H >- small_type{'x} } -->
   sequent ['ext] { 'H >- "type"{'x} }

(*
 * These are the types in the small universe.
 *)
interactive void_small 'H : :
   sequent ['ext] { 'H >- small_type{void} }

interactive unit_small 'H : :
   sequent ['ext] { 'H >- small_type{unit} }

interactive int_small 'H : :
   sequent ['ext] { 'H >- small_type{int} }

interactive dfun_small 'H 'z :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H; z: 'A >- small_type{'B['z]} } -->
   sequent ['ext] { 'H >- small_type{. a: 'A -> 'B['a]} }

interactive fun_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- small_type{'B} } -->
   sequent ['ext] { 'H >- small_type{. 'A -> 'B} }

interactive dprod_small 'H 'z :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H; z: 'A >- small_type{'B['z]} } -->
   sequent ['ext] { 'H >- small_type{. a: 'A * 'B['a]} }

interactive prod_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- small_type{'B} } -->
   sequent ['ext] { 'H >- small_type{. 'A * 'B} }

interactive union_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- small_type{'B} } -->
   sequent ['ext] { 'H >- small_type{. 'A + 'B} }

interactive equal_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'b = 'b in 'A } -->
   sequent ['ext] { 'H >- small_type{. 'a = 'b in 'A} }

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

let small_term = << small >>
let small_type_term = << small_type{'t} >>
let small_type_opname = opname_of_term small_type_term

let is_small_type_term =
   is_dep0_term small_type_opname

let mk_small_type_term =
   mk_dep0_term small_type_opname

let dest_small_type =
   dest_dep0_term small_type_opname

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Something is in a type if it is small.
 *)
let smallTypeT p =
   small_type_type (hyp_count_addr p) p

(*
 * Small is a type.
 *)
let d_small_typeT i p =
   if i = 0 then
      small_type (hyp_count_addr p) p
   else
      raise (RefineError ("d_small_typeT", StringTermError ("no elimination rule", small_type_term)))

let small_type_term = << "type"{small} >>

let d_resource = d_resource.resource_improve d_resource (small_type_term, d_small_typeT)

(*
 * Small intro.
 *)
let d_void_small_typeT i p =
   if i = 0 then
      void_small (hyp_count_addr p) p
   else
      raise (RefineError ("d_void_small_typeT", StringError "no elimination form"))

let void_small_type_term = << small_type{void} >>

let d_resource = d_resource.resource_improve d_resource (void_small_type_term, d_void_small_typeT)

let d_unit_small_typeT i p =
   if i = 0 then
      unit_small (hyp_count_addr p) p
   else
      raise (RefineError ("d_unit_small_typeT", StringError "no elimination form"))

let unit_small_type_term = << small_type{unit} >>

let d_resource = d_resource.resource_improve d_resource (unit_small_type_term, d_unit_small_typeT)

let d_int_small_typeT i p =
   if i = 0 then
      int_small (hyp_count_addr p) p
   else
      raise (RefineError ("d_int_small_typeT", StringError "no elimination form"))

let int_small_type_term = << small_type{int} >>

let d_resource = d_resource.resource_improve d_resource (int_small_type_term, d_int_small_typeT)

let d_dfun_small_typeT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         dfun_small (hyp_count_addr p) v p
   else
      raise (RefineError ("d_dfun_small_typeT", StringError "no elimination form"))

let dfun_small_type_term = << small_type{. a: 'A -> 'B['a] } >>

let d_resource = d_resource.resource_improve d_resource (dfun_small_type_term, d_dfun_small_typeT)

let d_fun_small_typeT i p =
   if i = 0 then
      fun_small (hyp_count_addr p) p
   else
      raise (RefineError ("d_fun_small_typeT", StringError "no elimination form"))

let fun_small_type_term = << small_type{. 'A -> 'B } >>

let d_resource = d_resource.resource_improve d_resource (fun_small_type_term, d_fun_small_typeT)

let d_dprod_small_typeT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         dprod_small (hyp_count_addr p) v p
   else
      raise (RefineError ("d_dprod_small_typeT", StringError "no elimination form"))

let dprod_small_type_term = << small_type{. a: 'A * 'B['a] } >>

let d_resource = d_resource.resource_improve d_resource (dprod_small_type_term, d_dprod_small_typeT)

let d_prod_small_typeT i p =
   if i = 0 then
      prod_small (hyp_count_addr p) p
   else
      raise (RefineError ("d_prod_small_typeT", StringError "no elimination form"))

let prod_small_type_term = << small_type{. 'A * 'B } >>

let d_resource = d_resource.resource_improve d_resource (prod_small_type_term, d_prod_small_typeT)

let d_union_small_typeT i p =
   if i = 0 then
      union_small (hyp_count_addr p) p
   else
      raise (RefineError ("d_union_small_typeT", StringError "no elimination form"))

let union_small_type_term = << small_type{. 'A + 'B } >>

let d_resource = d_resource.resource_improve d_resource (union_small_type_term, d_union_small_typeT)

let d_equal_small_typeT i p =
   if i = 0 then
      equal_small (hyp_count_addr p) p
   else
      raise (RefineError ("d_equal_small_typeT", StringError "no elimination form"))

let equal_small_type_term = << small_type{. 'a = 'b in 'A} >>

let d_resource = d_resource.resource_improve d_resource (equal_small_type_term, d_equal_small_typeT)

let smallAssumT i p =
   (tryT (rwh unfold_small_type 0) thenT equalAssumT i) p

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
