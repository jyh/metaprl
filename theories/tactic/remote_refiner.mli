(*
 * This module provide an interface to threads.
 * A constant number of threads is generated at startup,
 * and jobs can be submitted.
 *)

open Thread_refiner_sig

module MakeThreadRefiner (Arg : ThreadRefinerArgSig) (Remote : RemoteSig)
: ThreadRefinerSig
  with type extract = Arg.extract

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
