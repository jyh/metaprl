(*
 * The OCaml 4 stdlib functions under Latin1_case's names.  Used only
 * on OCaml 4 to regenerate latin1_case.expected; see run_latin1_case.sh.
 *)
let char_lowercase = Char.lowercase [@@ocaml.warning "-3"]
let char_uppercase = Char.uppercase [@@ocaml.warning "-3"]
let lowercase = String.lowercase [@@ocaml.warning "-3"]
let uppercase = String.uppercase [@@ocaml.warning "-3"]
let capitalize = String.capitalize [@@ocaml.warning "-3"]
let uncapitalize = String.uncapitalize [@@ocaml.warning "-3"]
