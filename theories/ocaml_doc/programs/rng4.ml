class linear_congruential_rng a c seed =
object (self)
    val mutable x = seed
    method next =
        x <- (x * a + c) land 0x3fffffff
    method next_int =
        self#next;
        x
    method next_float =
        self#next;
        (float_of_int x) /. (float_of_int 0x3fffffff)
end;;
