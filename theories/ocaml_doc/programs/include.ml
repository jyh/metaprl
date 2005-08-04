module type ASig = sig
    val x : bool
end;;

module type BSig = sig
    val x : int
end;;

module type CSig = sig
    include ASig
    include BSig
end;;

module A : ASig = struct
    let x = true
end;;

module B : BSig = struct
    let x = 1
end;;

module C : CSig = struct
    include A
    include B
end;;
