open Term
open Opname
open Num

let nuprl5_opname = mk_opname "!nuprl5_implementation!" nil_opname

(* parameter mapping *)

let make_bool_parameter b =
  make_param (ParmList
		[(make_param (Token "bool")); (make_param (Number (Num.Int (if b then 1 else 0))))])

let make_time_parameter time =
  make_param (ParmList
		[(make_param (Token "time")); (make_param (Number time))])

let time_parameter_p p =
  match (dest_param p) with
    ParmList [h; a; b] -> (match (dest_param h) with
      Token s -> if s = "time" then (match (dest_param a) with
	Number i -> (match (dest_param b) with
	  Number i -> true
      	| _ -> false)
      | _ -> false) else false
    | _ -> false)
  | _ -> false

let bool_parameter_p p =
  match (dest_param p) with
    ParmList [h; v] -> (match (dest_param h) with
      Token s -> if s = "bool" then (match (dest_param v) with
	Number (Num.Int i) -> (i = 1) or (i = 0)
      | _ -> false) else false
    | _ -> false)
  | _ -> false

let destruct_time_parameter p =
  match (dest_param p) with
    ParmList [h; n] -> (match (dest_param h) with
      Token s -> (if s = "time" then (match (dest_param n) with
	Number i -> i
      | _ -> raise (Invalid_argument "destruct_time_parameter_b"))
      else raise (Invalid_argument "destruct_time_parameter_c"))
    | _ -> raise (Invalid_argument "destruct_time_parameter_d"))
  | _ -> raise (Invalid_argument "destruct_time_parameter_e")


let destruct_bool_parameter p =
  match (dest_param p) with
    ParmList [h; v] -> (match (dest_param h) with
      Token s -> if s = "bool" then (match (dest_param v) with
	Number (Num.Int i) -> i = 1
      | _ -> raise (Invalid_argument "destruct_bool_parameter"))
      else raise (Invalid_argument "destruct_bool_parameter")
    | _ -> raise (Invalid_argument "destruct_bool_parameter"))
  | _ -> raise (Invalid_argument "destruct_bool_parameter")

(* common terms *)

(*
let itoken_term s = mk_token_term nuprl5_opname s
let inatural_term i = mk_number_term nuprl5_opname i
*)

 

