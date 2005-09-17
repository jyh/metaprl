class choose_rng =
  let a, c, m, seed = 314159262, 1, 0x3fffffff, 17 in
  object (self)
      val mutable x = seed
      method private next =
          x <- (x * a + c) land m
      method choose : 'a. 'a array -> 'a = fun elements ->
          self#next;
          elements.(x mod Array.length elements)
  end;;
