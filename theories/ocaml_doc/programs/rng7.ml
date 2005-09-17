class skip_rng skip =
  let a, c, m, seed = 314159262, 1, 0x3fffffff, 1 in
  object (self)
      val mutable x = seed
      method private next =
          x <- (x * a + c) land m
      method next_int = self#next; x
      initializer
          for i = 1 to skip do
              self#next
          done;
          Printf.printf "rng state: %d\n" x
  end;;
