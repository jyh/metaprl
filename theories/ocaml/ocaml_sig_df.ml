(*
 * Display forms for signature items.
 *)

include Ocaml
include Ocaml_base_df
include Ocaml_expr_df

open Debug
open Printf

let _ =
   if !debug_load then
      eprintf "Loading Ocaml_sig_df%t" eflush

(*
 * Display instructions.
 *)
declare sig_type_next
declare sig_name
declare sig_slt

(*
 * Signatures and structures are treated as records.
 * Their names are strings, not variables, and they do not
 * alpha-vary.  We could have external and internal names
 * like Harper's translucent sums, but we would diverge
 * from the ocaml type theory.
 *)

(*
 * Exception declarations name type constructors.
 *)
dform sig_exception_df : sig_exception[@name:s]{'tl} =
   szone push_indent "exception" space slot[@name:s] space "of"
   space slot{type_prod; 'tl}

(*
 * External function declaration.
 *)
dform sig_external_df : sig_external[@name:s]{'t; 'sl} =
   szone push_indent "external" space slot[@name:s] space
   ":" space slot{'t}
   "=" space slot{list_expr; 'sl}

(*
 * Module declaration.
 *)
dform sig_module_df : sig_module[@name:s]{'mt} =
   "module" space slot[@name] space ":" space slot{'mt}

(*
 * Module type declaration.
 *)
dform sig_module_type_df : sig_module_type[@name:s]{'mt} =
   "moduletype" space slot[@name] space "=" space slot{'mt}

(*
 * Open a module in scope.
 *)
dform sig_open_df : sig_open{'sl} =
   "open" space slot{list_expr; 'sl}

(*
 * Type definition.
 *)
dform sig_type_df : sig_type{'ssltl} =
   szone pushm[0] "type" slot{sig_type; 'ssltl} popm ezone

dform sig_type_nil_df : slot{sig_type; nil} = `""

dform sig_type_cons_df : slot{sig_type; cons{'sslt; 'ssltl}} =
   slot{sig_type; 'sslt; 'ssltl}

dform sig_type_next_nil_df : slot{sig_type_next; nil} = `""

dform sig_type_next_cons_df : slot{sig_type_next; cons{'sslt; 'ssltl}} =
   sbreak "and" space slot{sig_type; 'sslt; 'ssltl}

dform sig_type_cons_df : slot{sig_type; cons{'s; 'slt}; 'ssltl} =
   slot{sig_name; 's} space "=" slot{sig_slt; 'slt} slot{sig_type_next; 'ssltl}

dform sig_name_string_df : slot{sig_name; string[@s:s]} =
   slot[@s:s]

dform sig_slt_cons_df : slot{sig_slt; cons{'s; 'slt}} =
   slot{sig_slt; 's; 'slt}

dform sig_slt_string_df : slot{sig_slt; string[@s:s]; 'slt} =
   "'" slot[@s:s] space slot{sig_slt; 'slt}

dform sig_slt_type_df : slot{sig_slt; sig_type{'t}} =
   slot{'t}

(*
 * Value declaration.
 *)
dform sig_value_df : sig_value[@name:s]{'t} =
   szone push_indent slot[@name:s] space ":" space slot{'t} popm ezone

(*
 * $Log$
 * Revision 1.4  1998/04/29 20:54:09  jyh
 * Initial working display forms.
 *
 * Revision 1.3  1998/04/29 14:49:22  jyh
 * Added ocaml_sos.
 *
 * Revision 1.2  1998/02/18 18:47:42  jyh
 * Initial ocaml semantics.
 *
 * Revision 1.1  1998/02/13 16:02:23  jyh
 * Partially implemented semantics for caml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
