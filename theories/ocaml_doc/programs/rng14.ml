class linear_rng =
  object (self)
      val a = 314159262
      val c = 1
      val m = 0x3fffffff
      val mutable x = 2
      method private next =
          x <- (x * a + c) land m
      method next_int =
          self#next;
          x
      method next_float =
          self#next;
          float_of_int x /. float_of_int m
  end;;

class quadratic_rng =
   object 
       inherit linear_rng
       method private next =
           x <- (x * (x + 1)) land m
       method print =
           print_string ("x = " ^ string_of_int x)
   end;;

let choose (rng : linear_rng) elements () =
    elements.(rng#next_int mod Array.length elements);;

let g = choose (new quadratic_rng) [|"Red"; "Green"; "Blue"|];;
