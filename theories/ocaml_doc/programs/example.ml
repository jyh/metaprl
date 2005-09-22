class virtual a =
object
    method private virtual f : unit
end

class b =
object
    inherit a
    method private f =
       print_string "b\n"
end

class c =
object
    inherit a
    method private f =
        print_string "c\n"
end

class d =
object
    val mutable x : b = new b
    method setx y =
        x <- y
    method getx =
        x
end

let z = (new c :> b);;
let z = new d;;
z#setx (new c);;
z#getx;;
