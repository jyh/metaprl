class new_rng rand_seed =
  let a, c, m = 314159262, 1, 0x3fffffff in
  let seed =
      if rand_seed
      then int_of_float (Unix.gettimeofday ())
      else 1
  in
  let normalize x = (float_of_int x) /. (float_of_int m) in
  object (self)
      val mutable x = seed
      method private next =
          x <- (x * a + c) land m
      method next_int =
          self#next;
          x
      method next_float =
          self#next;
          normalize x
  end;;
