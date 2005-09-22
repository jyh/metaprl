    class b =
    object
        method f =
           print_string "b\n"
    end
    
    class c =
    object
        val s = "c\n"
        method f =
           print_string s
    end
    
    let z = [new c; new b]
