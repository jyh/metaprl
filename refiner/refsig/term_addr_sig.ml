(*
 *
 *)

module type TermAddrSig =
sig
   type term
   type address

   (* Subterm addressing *)
   exception IncorrectAddress of address * term

   (*
    * Constructors.
    *)
   val make_address : int list -> address
   val compose_address : address -> address -> address

   (*
    * These constructors are specifically for sequents.
    *   nth_hd_address n: address of the nth clause
    *   nth_tl_address n: address of all clauses n and larger
    *)
   val nth_hd_address : int -> address
   val nth_tl_address : int -> address

   (*
    * Destructors.
    *)
   val string_of_address : address -> string

   (*
    * Addressed operations.
    *)
   val term_subterm :  term -> address -> term
   val replace_subterm : term -> address -> term -> term
   val apply_fun_at_addr : (term -> term) -> address -> (term -> term)
   val apply_fun_arg_at_addr : (term -> term * 'a) -> address -> (term -> term * 'a)
end

(*
 * $Log$
 * Revision 1.6  1998/06/22 19:45:45  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.5  1998/06/12 13:47:05  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.4  1998/06/03 22:19:27  jyh
 * Nonpolymorphic refiner.
 *
 * Revision 1.3  1998/06/03 15:23:24  jyh
 * Generalized many the term_addr, term_man, and term_shape modules.
 *
 * Revision 1.2  1998/06/01 13:55:12  jyh
 * Proving twice one is two.
 *
 * Revision 1.1  1998/05/28 15:01:42  jyh
 * Partitioned refiner into subdirectories.
 *
 * Revision 1.1  1998/05/27 15:14:18  jyh
 * Functorized the refiner over the Term module.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
