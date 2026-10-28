(*
 * Case conversion on ISO-8859-1 (Latin-1) strings.
 *
 * These are the semantics of the OCaml 4 stdlib functions
 * String.lowercase, String.uppercase, String.capitalize,
 * String.uncapitalize, Char.lowercase and Char.uppercase, which
 * OCaml 5 removed.  Their replacements (the *_ascii functions) leave
 * the Latin-1 letters unchanged, so MetaPRL uses these instead and
 * its behaviour does not change.
 *)
val char_lowercase : char -> char
val char_uppercase : char -> char
val lowercase : string -> string
val uppercase : string -> string
val capitalize : string -> string
val uncapitalize : string -> string
