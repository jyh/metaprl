class ['a] choose_rng elements =
  let a, c, m, seed = 314159262, 1, 0x3fffffff, 17 in
  let length = Array.length elements in
  object (self)
      val mutable x = seed
      method private next =
          x <- (x * a + c) land m
      method choose : 'a =
          self#next;
          elements.(x mod length)
  end;;
