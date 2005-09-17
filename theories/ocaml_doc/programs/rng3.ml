class linear_congruential_rng a c seed =
object
    val mutable x = seed
    method next_int =
        x <- (x * a + c) land 0x3fffffff;
        x
    method next_float =
        x <- (x * a + c) land 0x3fffffff;
        (float_of_int x) /. (float_of_int 0x3fffffff)
end;;
