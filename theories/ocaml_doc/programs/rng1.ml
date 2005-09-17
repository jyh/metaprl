class linear_congruential_rng =
object
    val mutable x = 1
    method next =
        x <- (x * 314159262 + 1) land 0x3fffffff;
        x
end;;
