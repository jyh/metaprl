extends Itt_struct
extends Itt_int_ext
extends Itt_int_arith
extends Itt_supinf
extends Itt_omega

open Basic_tactics
open Tactic_type.Tactic

topval testT : tactic

(*
 * this tactic generates an artificial example used in testn
 *)
topval genT : term list -> int -> int -> int -> int -> int -> tactic
