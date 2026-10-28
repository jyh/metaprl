(*
 * Case conversion on ISO-8859-1 (Latin-1) strings, with the
 * semantics of the OCaml 4 stdlib functions OCaml 5 removed.
 * See latin1_case.mli.
 *)
let char_lowercase c =
   if (c >= 'A' && c <= 'Z')
      || (c >= '\192' && c <= '\214')
      || (c >= '\216' && c <= '\222')
   then
      Char.unsafe_chr (Char.code c + 32)
   else
      c

let char_uppercase c =
   if (c >= 'a' && c <= 'z')
      || (c >= '\224' && c <= '\246')
      || (c >= '\248' && c <= '\254')
   then
      Char.unsafe_chr (Char.code c - 32)
   else
      c

let lowercase s = String.map char_lowercase s
let uppercase s = String.map char_uppercase s

let apply1 f s =
   if s = "" then
      s
   else
      let b = Bytes.of_string s in
         Bytes.set b 0 (f (Bytes.get b 0));
         Bytes.to_string b

let capitalize s = apply1 char_uppercase s
let uncapitalize s = apply1 char_lowercase s
