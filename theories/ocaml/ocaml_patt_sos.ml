(*
 * Pattern semantics.
 * Patterns are the same if they have the same syntax.
 *)

open Ocaml
open Ocaml_base_sos

(*
 * Constants.
 *)
axiom patt_char_equiv :
   sequent { 'H >- equiv{'S; 'p1; 'p2} } -->
   sequent { 'H >- equiv{'S; patt_char[$c:s]{'p1}; patt_char[$c:s]{'p2}} }

axiom patt_int_equiv :
   sequent { 'H >- equiv{'S; 'p1; 'p2} } -->
   sequent { 'H >- equiv{'S; patt_int[$i:n]; patt_int[$i:n]} }

(*
 * Variables must be the same.
 *)
axiom patt_var_equiv :
   sequent { 'H; x: term >- equiv{'S; 'p1; 'p2} }
(*
 * $Log$
 * Revision 1.1  1998/02/13 16:02:21  jyh
 * Partially implemented semantics for caml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
