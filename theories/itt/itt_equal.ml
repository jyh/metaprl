(*
 * Equality type.
 *
 *)

open Debug
open Opname
open Term
open Rformat
open Simple_print
open Refine_sig
open Resource

open Tactic_type

include Base_theory

(* debug_string DebugLoad "Loading itt_equal..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare ext
declare squash

declare "type"{'a}
declare univ[@i:l]
declare equal{'T; 'a; 'b}
declare it

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform equal{'T; 'a; 'b} =
   szone pushm slot{'a} space `"= " slot{'b} space `"in " slot{'T} popm ezone
dform mode[prl] :: it = cdot

dform mode[prl] :: "type" = `"Type"

mldform mode[prl] :: univ[@i:l] term_print buf =
   format_char buf '\134';
   format_simple_level_exp buf i

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext a = b in T
 * by equalityFormation T
 *
 * H >- T ext a
 * H >- T ext b
 *)
prim equalityFormation 'H 'T :
   ('a : sequent [ext] { 'H >- 'T }) -->
   ('b : sequent [ext] { 'H >- 'T }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   'a = 'b in 'T

(*
 * H >- (a1 = b1 in T1) = (a2 = b2 in T2)
 * by equalityEquality
 *
 * H >- T1 = T2 in Ui
 * H >- a1 = a2 in T1
 * H >- b1 = b2 in T1
 *)
prim equalityEquality 'H :
   sequent [squash] { 'H >- 'T1 = 'T2 in univ[@i:l] }
   sequent [squash] { 'H >- 'a1 = 'a2 in 'T1 }
   sequent [squash] { 'H >- 'b1 = 'b2 in 'T2 } :
   sequent ['ext] { 'H >- ('a1 = 'b1 in 'T1) = ('a2 = 'b2 in 'T2) in univ[@i:l] } =
   it

(*
 * H >- it = it in (a = b in T)
 * by axiomEquality
 *
 * H >- a = b in T
 *)
prim axiomEquality 'H : 
   sequent [squash] { 'H >- 'a = 'b in 'T } :
   sequent ['ext] { 'H >- it = it in ('a = 'b in 'T) } =
   it

(*
 * H, x: a = b in T, J[x] >- C[x]
 * by equalityElimination i
 *
 * H, x: a = b in T; J[it] >- C[it]
 *)
prim equalityElimination 'H 'J :
   ('t : sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J[it] >- 'C[it] }) :
   sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J['x] >- 'C['x] } =
   't

(*
 * H >- T = T in type
 * by typeEquality
 *
 * H >- T
 *)
prim typeEquality 'H :
   sequent [squash] { 'H >- 'T } :
   sequent ['ext] { 'H >- "type"{'T} } =
   it

(*
 * There should be only one param, of String type.
 * Get it. 
 *)
let dest_level_param t =
   let { term_op = op } = dest_term t in
      match dest_op op with 
         { op_params = [param] } ->
            begin
               match dest_param param with
                  Level s -> s
                | _ -> raise (TermMatch ("dest_level_param", t, "param type"))
            end
       | { op_params = [] } ->
            raise (TermMatch ("dest_level_param", t, "no params"))
       | _ ->
            raise (TermMatch ("dest_level_param", t, "too many params"))

(* Cumulativity over universes *)
mlterm cumulativity{univ[@j:l]; univ[@i:l]} =
   let i = dest_level_param <:con< univ[@i:l] >> in
   let j = dest_level_param <:con< univ[@j:l] >> in
      if level_cumulativity j i then
         []
      else
         raise (RefineError (StringError "cumulativity"))

(*
 * H >- Uj = Uj in Ui
 * by universeEquality (side (j < i))
 *)
prim universeEquality 'H :
   cumulativity{univ[@j:l]; univ[@i:l]} :
   sequent ['ext] { 'H >- univ[@j:l] = univ[@j:l] in univ[@i:l] } =
  it

(*
 * H >- Ui ext Uj
 * by universeFormation
 *)
prim universeFormation 'H univ[@j:l] : 
   cumulativity{univ[@j:l]; univ[@i:l]} :
   sequent ['ext] {'H >- univ[@i:l] } =
   univ[@j:l]

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

(*
 * Primitives.
 *)
let equal_opname =
   let t = << 'a = 'b in 'c >> in
      opname_of_term t

let is_equal_term = is_dep0_dep0_dep0_term equal_opname
let dest_equal = dest_dep0_dep0_dep0_term equal_opname
let mk_equal_term = mk_dep0_dep0_dep0_term equal_opname

(*
 * EQCD resource.
 * The key is the opname plus the arity of the subterms.
 *)
type eqcd_key = opname * int list

type eqcd_data =
   { eqcd_info : (eqcd_key * tactic) list;
     mutable eqcd_table : (eqcd_key, tactic) Hashtbl.t option
   }

resource (term * tactic, tactic, eqcd_data) eqcd_resource

(*
 * Check if the first list is a suffix of the other.
 *)
let check_suffix list1 =
   let rec aux l =
      if list1 == l then
         true
      else
         match l with
            _::t ->
               aux t
          | [] ->
               false
   in
      aux

(*
 * Insert the first list into the second.
 *)
let rec insert_data data1 = function
   h::t ->
      begin
         match h with
            name, tac ->
               begin
                  try 
                     List.assq name data1;
                     insert_data data1 t
                  with
                     Not_found ->
                        insert_data (h::data1) t
               end
      end
      
 | [] -> data1
            
(*
 * Join the data from two bases.
 * First check if one is a suffix of the other.
 * This will commonly be the case, and so we optimize it.
 *)
let join_data base1 base2 =
   let data1 = base1.eqcd_info in
   let data2 = base2.eqcd_info in
      if check_suffix data1 data2 then
         base2
      else if check_suffix data2 data1 then
         base1
      else
         { eqcd_info = insert_data data2 data1; eqcd_table = None }

(*
 * Compute the hashtable from the info.
 *)
let compute_table info =
   let tbl = Hashtbl.create (List.length info) in
   let aux (key, tac) =
      Hashtbl.add tbl key tac
   in
      List.iter aux info;
      tbl

(*
 * Extract a D tactic from the data.
 * The tactic checks for an optable.
 *)
let extract_data base =
   let eqcd p =
      let tbl =
         (* Compute the hashtbl if necessary *)
         match base.eqcd_table with
            None ->
               let tbl = compute_table base.eqcd_info in
                  base.eqcd_table <- Some tbl;
                  tbl
          | Some tbl -> tbl
      in
      let t = concl p in
      let _, l, _ = dest_equal t in
      let key = opname_of_term l, subterm_arities l in
         try
            (* Find and apply the right tactic *)
            let tac = Hashtbl.find tbl key in
               tac p
         with
            Not_found ->
               raise (RefineError (StringError ("EQCD tactic doesn't know about " ^ (string_of_opname (fst key)))))
   in
      eqcd

(*
 * Add a new tactic.
 *)
let improve_data (t, tac) data =
   { eqcd_info = ((opname_of_term t, subterm_arities t), tac)::(data.eqcd_info);
     eqcd_table = None
   }

(*
 * Wrap up the joiner.
 *)
let rec join_resource base1 base2 =
   let data = join_data base1.resource_data base2.resource_data in
      { resource_data = data;
        resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource
      }
      
and extract_resource { resource_data = data } =
   extract_data data
   
and improve_resource { resource_data = data } x =
   { resource_data = improve_data x data;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * Resource.
 *)
let eqcd_resource =
   { resource_data = { eqcd_info = []; eqcd_table = None };
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

let eqcd = eqcd_resource.resource_extract eqcd_resource

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D tactic.
 *)
let d_equal i p =
   if i = 0 then
      failwith "Use EqCD on conclusion"
   else
      let t = goal p in
      let count = num_hyps t in
         equalityElimination (i - 1) (count - i - 1) p

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:52:10  jyh
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
 * Revision 1.7  1996/10/23 15:18:06  jyh
 * First working version of dT tactic.
 *
 * Revision 1.6  1996/09/25 22:52:11  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.5  1996/09/02 19:37:21  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.4  1996/05/21 02:16:43  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.3  1996/04/11 13:33:57  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.2  1996/03/28 02:51:29  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.1  1996/03/05 19:59:42  jyh
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
