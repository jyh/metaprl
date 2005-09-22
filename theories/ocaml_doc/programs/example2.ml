class point =
   object
     val x = 0
     method get_x = x
   end;;

class colored_point =
   object
      inherit point
      val color = "Red"
      method get_x = x + 1
(*
      method get_color =
         print_string "g\n"
*)
   end;;

let l = [new point; new colored_point]
