
open Refiner.Refiner.Term
open Tactic_type.Conversionals

(*
declare orderSig[i:l]

declare IrreflexiveOrder[i:l]

declare TransitiveOrder[i:l]

declare PartialOrder[i:l]
*)
declare preorder[i:l]
declare order[i:l]

declare DecEquality[i:l]

declare compare{'self; 'a;'b; 'less_case; 'equal_case; 'greater_case}

declare less{'self; 'a;'b}
declare eq{'self; 'a;'b}

declare int_order

topval decideOrder3T : term -> term -> tactic

topval  hypTransT  : int -> int -> tactic

declare type_product_ord{'T;'Ord}
