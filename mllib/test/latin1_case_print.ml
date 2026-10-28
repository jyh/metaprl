(*
 * Print the result of every Latin1_case function on every byte, as
 * hex, one line per input.  Compiled against latin1_case.ml this
 * checks the module; compiled against latin1_case_ocaml4.ml on
 * OCaml 4 (which still has the old stdlib functions) it produces the
 * expected output, latin1_case.expected.
 *)
let hex s =
   String.concat "" (List.map (fun c -> Printf.sprintf "%02x" (Char.code c))
                        (List.init (String.length s) (String.get s)))

let () =
   for i = 0 to 255 do
      let c = Char.chr i in
      let s = String.make 1 c in
      let s2 = String.make 1 c ^ "\xe9" in
         Printf.printf "%02x cl=%02x cu=%02x l=%s u=%s c=%s uc=%s c2=%s uc2=%s\n"
            i
            (Char.code (Latin1_case.char_lowercase c))
            (Char.code (Latin1_case.char_uppercase c))
            (hex (Latin1_case.lowercase s))
            (hex (Latin1_case.uppercase s))
            (hex (Latin1_case.capitalize s))
            (hex (Latin1_case.uncapitalize s))
            (hex (Latin1_case.capitalize s2))
            (hex (Latin1_case.uncapitalize s2))
   done;
   Printf.printf "empty c=%s uc=%s l=%s u=%s\n"
      (hex (Latin1_case.capitalize ""))
      (hex (Latin1_case.uncapitalize ""))
      (hex (Latin1_case.lowercase ""))
      (hex (Latin1_case.uppercase ""))
