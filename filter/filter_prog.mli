(*
 * Conversion form filter_summary to program text.
 *)

open Filter_type
open Filter_summary_type
open Filter_summary
open Filter_cache

val extract_sig :
   (unit, MLast.ctyp, MLast.expr, MLast.sig_item) module_info ->
   (module_path * MLast.ctyp resource_info) list ->
   string -> (MLast.sig_item * (int * int)) list
   
val extract_str :
   (proof_type, MLast.ctyp, MLast.expr, MLast.str_item) module_info ->
   (module_path * MLast.ctyp resource_info) list ->
   string -> (MLast.str_item * (int * int)) list

(*
 * $Log$
 * Revision 1.5  1998/04/15 12:40:01  jyh
 * Updating editor packages to Filter_summarys.
 *
 * Revision 1.4  1998/04/13 17:08:36  jyh
 * Adding interactive proofs.
 *
 * Revision 1.3  1998/04/09 18:25:52  jyh
 * Working compiler once again.
 *
 * Revision 1.2  1998/02/23 14:46:16  jyh
 * First implementation of binary file compilation.
 *
 * Revision 1.1  1998/02/21 20:57:49  jyh
 * Two phase parse/extract.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
