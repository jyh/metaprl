(* unit-link: filter *)
(*
 * Filter_shape (filter/base): the opname shape classes (a bit field of
 * iform and const), their predicates, their num form and how they print.
 * A class is "normal" when it is not an iform, so const alone is normal.
 *
 * No build or census reaches the predicates on a combined class, the
 * num conversions or pp_print_shape_class.
 *
 * The expected file is the output of the code.
 *)
open Filter_shape

let pr sc = pp_print_shape_class Lm_printf.str_formatter sc; Lm_printf.flush_str_formatter ()

let () =
   List.iter (fun (name, sc) ->
         Printf.printf "%-14s normal %b  iform %b  const %b  num %s  prints %S\n" name
            (is_shape_normal sc) (is_shape_iform sc) (is_shape_const sc)
            (Lm_num.string_of_num (num_of_shape_class sc)) (pr sc))
      [ "normal", shape_normal; "iform", shape_iform; "const", shape_const;
        "iform+const", shape_combine shape_iform shape_const;
        "normal+normal", shape_combine shape_normal shape_normal;
        "from num 3", shape_class_of_num (Lm_num.num_of_int 3) ]
