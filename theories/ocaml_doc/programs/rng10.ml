class ['a] choose_rng =
  let a, c, m, seed = 314159262, 1, 0x3fffffff, 17 in
  object (self)
      val mutable x = seed
      method private next =
          x <- (x * a + c) land m
      method choose (elements : 'a array) : 'a =
          self#next;
          elements.(x mod Array.length elements)
  end;;
