(*
 * This is the null thread implementation.
 *)

open Remote_sig
open Thread_refiner_sig

module MakeThreadRefiner (Arg : ThreadRefinerArgSig) (Remote : RemoteSig) : ThreadRefinerSig
with type extract = Arg.extract

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
