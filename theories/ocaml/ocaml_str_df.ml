(*
 * Display forms for structure items.
 *)

include Ocaml
include Ocaml_base_df
include Ocaml_sig_df

open Debug
open Printf

let _ =
   if !debug_load then
      eprintf "Loading Ocaml_str_df%t" eflush

(*
 * Exception declarations name type constructors.
 *)
dform str_exception_df : str_exception[@name:s]{'tl} =
   sig_exception[@name:s]{'tl}

(*
 * External function declaration.
 *)
dform str_external_df : str_external[@name:s]{'t; 'sl} =
   sig_external[@name:s]{'t; 'sl}

(*
 * Unnamed value.
 *)
dform str_expr_df : str_expr{'e} =
   szone push_indent "let" space "_" space "=" space slot{'e} popm ezone

(*
 * Module definition.
 *)
dform str_module_df : str_module[@name:s]{'me} =
   szone push_indent "module" space slot[@name] space "=" space slot{'me}

(*
 * Module type definition.
 *)
dform str_module_type_df : str_module_type[@name:s]{'mt} =
   sig_module_type[@name:s]{'mt}

(*
 * Open a module in scope.
 *)
dform str_open_df1 : str_open{'sl} = 
   sig_open{'sl}

dform str_open_df2 : str_open[@start:n, @finish:n]{'sl} =
   str_open{'sl}

(*
 * Type definition.
 *)
dform str_type_df : str_type{'ssltl} =
   sig_type{'ssltl}

(*
 * Value definition.
 *)
dform str_let_df : str_let{'p; 'e} = "let"{'p; 'e}
                          
(*
 * $Log$
 * Revision 1.5  1998/04/30 14:20:34  jyh
 * Updating term_table.
 *
 * Revision 1.4  1998/04/29 20:54:11  jyh
 * Initial working display forms.
 *
 * Revision 1.3  1998/04/29 14:49:26  jyh
 * Added ocaml_sos.
 *
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
