(*
 * Display forms for signature items.
 *)

include Ocaml
include Ocaml_base_df

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
dform sig_exception[$name:s]{'tl} =
   szone push_indent "exception" space slot[$name:s] space "of"
   space slot{type_prod; 'tl}

(*
 * External function declaration.
 *)
dform sig_external[$name:s]{'t; 'sl} =
   szone push_indent "external" space slot[$name:s] space
   ":" space slot{'t}
   "=" space slot{string_list; 'sl}

(*
 * Module declaration.
 *)
dform sig_module[$name:s]{'mt} =
   "module" space slot[$name] space ":" space slot{'mt}

(*
 * Module type declaration.
 *)
dform sig_module_type[$name:s]{'mt} =
   "module type" space slot[$name] space "=" space slot{'mt}

(*
 * Open a module in scope.
 *)
dform sig_open{'sl} =
   "open" space slot{string_list; 'sl}

(*
 * Type definition.
 *)
dform sig_type{'ssltl} =
   szone pushm "type" slot{sig_type; 'ssltl} popm ezone

dform slot{sig_type; nil} = ""

dform slot{sig_type; cons{'sslt; 'ssltl}} =
   slot{sig_type; 'sslt; 'ssltl}

dform slot{sig_type_next; nil} = ""

dform slot{sig_type_next; cons{'sslt; 'ssltl}} =
   sbreak "and" space slot{sig_type; 'sslt; 'ssltl}

dform slot{sig_type; cons{'s; 'slt}; 'ssltl} =
   slot{sig_name; 's} space "=" slot{sig_slt; 'slt} slot{sig_type_next; 'ssltl}

dform slot{sig_name; string[$s:s]} =
   slot[$s:s]

dform slot{sig_slt; cons{'s; 'slt}} =
   slot{sig_slt' 's; 'slt}

dform slot{sig_slt; string[$s:s]; 'slt} =
   "'" slot[$s:s] space slot{sig_slt; 'slt}

dform slot{sig_slt; sig_type{'t}} =
   slot{'t}

(*
 * Value declaration.
 *)
dform sig_value[$name:s]{'t} =
   szone push_indent slot[$name:s] space ":" space slot{'t} popm ezone

(*
 * $Log$
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
