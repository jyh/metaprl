extends Base_theory

open Lm_debug
open Printf

open Tactic_type
open Top_conversionals
open Dtactic
open Tactic_type.Conversionals
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermOp
open Refiner.Refiner.Term
open Refiner.Refiner.RefineError

open Term_stable
open Tactic_type.Tacticals
open Tactic_type.Conversionals


(* Commutative Resource *)

let extract_data tbl =
   let rw e =
      let t = env_term e in
         try
            slookup tbl t
         with
            Not_found ->
               raise (RefineError ("Support_algebra.extract_data", StringTermError ("Commutative resource does not know about", t)))
   in
      funC rw

let resource commutative =
   stable_resource_info extract_data

let symC =
 funC (fun env ->
  Sequent.get_resource_arg (env_arg env) get_commutative_resource
      )

(* Associative Resource *)

let id tbl = tbl

let resource associative =
   stable_resource_info id

let revAssocC =
 funC (fun env ->
   let term = (env_term env) in
         try
            let table = Sequent.get_resource_arg (env_arg env) get_associative_resource in
            let (_,revAssocC) = slookup table term in  revAssocC
         with
            Not_found ->
               raise (RefineError ("revAssocC", StringTermError ("Associative resource does not know about", term)))
      )


let assocC =
 funC (fun env ->
   let term = (env_term env) in
         try
            let table = Sequent.get_resource_arg (env_arg env) get_associative_resource in
            let (assocC,_) = slookup table term in assocC
         with
            Not_found ->
               raise (RefineError ("assocC", StringTermError ("Associative resource does not know about", term)))
      )


let subAssocC_1 first length opname revAssocC conv  =
   let rec sub0C length = (* invariant: sub0C always applies to an opname term *)
     if length > 1 then
        revAssocC thenC sub0C (length-1)
        orelseC if length = 2 then conv else failC
     else if length = 1 then
        addrC [0] conv
     else failC
  in
  let rec subNC first =  termC (fun term ->
     if opname_of_term term <> opname then
        if first=0 && length=1 then conv else failC
     else
        if first>0 then
           addrC [1] (subNC (first -1) )
        else if first = 0 then
           sub0C length
        else failC )
  in
     subNC first


let subAssocC first length conv  =
   funC (fun env ->
   let term = (env_term env) in
   let opname = opname_of_term term  in
      try
         let table = Sequent.get_resource_arg (env_arg env) get_associative_resource in
         let (_,revAssocC) = slookup table term in
            subAssocC_1 first length opname revAssocC conv
      with Not_found ->
               raise (RefineError ("subAssocC", StringTermError ("Associative resource does not know about", term)))
)

let rec addrAssocC addr conv =
   funC (fun env ->
   let term = (env_term env) in
   let opname = opname_of_term term  in
   let ussualC ()=
      match addr with
            [] -> conv |
            n::rest -> addrC [n] (addrAssocC rest conv)
   in
   let specialC revAssocC =
      match addr with
            [] -> conv |
            first::length::rest -> subAssocC_1 first length opname revAssocC (addrAssocC rest conv) |
            _ -> failC
   in
      try
         let table = Sequent.get_resource_arg (env_arg env) get_associative_resource in
         let (_,revAssocC) = slookup table term in
            specialC revAssocC
      with _ -> ussualC ()
)

