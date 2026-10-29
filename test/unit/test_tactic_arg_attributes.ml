(* The proof editor re-attaches a stored sub-proof to a new subgoal only
   when Tactic_boot's tactic_arg_alpha_equal_with_attributes says the two
   tactic arguments are equal: the same goal and the same attributes
   ("Proof steps match only if the annotations match", 6eaa4919b).  This
   test builds tactic arguments with the same goal that differ in one
   attribute of each kind it compares, and prints the comparison. *)
open Refiner.Refiner
open Tactic_boot

let op s = Opname.make_opname [ s ]
let t name = Term.mk_simple_term (op name) []
let goal = Refine.mk_msequent (t "C") []

let arg attrs =
  { TacticInternalType.ref_goal = goal;
    ref_label = "main";
    ref_attributes = TacticInternal.attribute_info_of_raw_attributes attrs;
    ref_bookmark = Mp_resource.empty_bookmark;
    ref_sentinal = Tactic.null_sentinal }

let show name a b =
  Printf.printf "%-40s %s\n" name
    (if TacticInternal.tactic_arg_alpha_equal_with_attributes (arg a) (arg b) then "equal" else "different")

let () =
  show "no attributes" [] [];
  show "term a, term a" [ Tactic.term_attribute "x" (t "a") ] [ Tactic.term_attribute "x" (t "a") ];
  show "term a, term b" [ Tactic.term_attribute "x" (t "a") ] [ Tactic.term_attribute "x" (t "b") ];
  show "term list [a], term list [a]" [ Tactic.term_list_attribute "l" [ t "a" ] ] [ Tactic.term_list_attribute "l" [ t "a" ] ];
  show "term list [a], term list [b]" [ Tactic.term_list_attribute "l" [ t "a" ] ] [ Tactic.term_list_attribute "l" [ t "b" ] ];
  show "term list [a], term list [a; b]" [ Tactic.term_list_attribute "l" [ t "a" ] ] [ Tactic.term_list_attribute "l" [ t "a"; t "b" ] ];
  show "int 1, int 2" [ Tactic.int_attribute "i" 1 ] [ Tactic.int_attribute "i" 2 ];
  show "type a, type b" [ Tactic.type_attribute "y" (t "a") ] [ Tactic.type_attribute "y" (t "b") ]
