(*
 * Display forms for structure items.
 *)

include Ocaml
include Ocaml_base_df
include Ocaml_sig_df

(*
 * Exception declarations name type constructors.
 *)
dform str_exception[@name:s]{'tl} =
   sig_exception[@name:s]{'t}

(*
 * External function declaration.
 *)
dform str_external[@name:s]{'t; 'sl} =
   sig_external[@name:s]{'t; 'sl}

(*
 * Unnamed value.
 *)
dform str_expr{'e} =
   szone push_indent "let" space "_" space "=" space slot{'e} popm ezone

(*
 * Module definition.
 *)
dform str_module[@name:s]{'me} =
   szone push_indent "module" space slot[@name] space "=" space slot{'me}

(*
 * Module type definition.
 *)
dform str_module_type[@name:s]{'mt} =
   sig_module_type[@name:s]{'mt}

(*
 * Open a module in scope.
 *)
dform str_open{'sl} = 
   str_open{'sl}

(*
 * Type definition.
 *)
dform str_type{'ssltl} =
   sig_type{'ssltl}

(*
 * Value definition.
 *)
dform str_let{'p; 'e} = "let"{'p; 'e}
                          
(*
 * $Log$
 * Revision 1.2  1998/02/18 18:47:49  jyh
 * Initial ocaml semantics.
 *
 * Revision 1.1  1998/02/13 16:02:24  jyh
 * Partially implemented semantics for caml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
