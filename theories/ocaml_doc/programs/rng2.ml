class linear_congruential_rng a c seed =
object
    val mutable x = seed
    method next =
        x <- (x * a + c) land 0x3fffffff;
        x
end;;
