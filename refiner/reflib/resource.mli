(*
 * Resource management.
 * Each resource provides four operations:
 *    1. Create a new, empty resource
 *    2. Join two resource providers
 *    3. Extract a value from the resource
 *    4. Add a value to the resource
 *
 *)

type ('a, 'b, 'c) rsrc =
   { resource_data : 'c;
     resource_join : ('a, 'b, 'c) rsrc -> ('a, 'b, 'c) rsrc -> ('a, 'b, 'c) rsrc;
     resource_extract : ('a, 'b, 'c) rsrc -> 'b;
     resource_improve : ('a, 'b, 'c) rsrc -> 'a -> ('a, 'b, 'c) rsrc;
     resource_close : ('a, 'b, 'c) rsrc -> ('a, 'b, 'c) rsrc
   }

val debug_resource : bool ref

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
