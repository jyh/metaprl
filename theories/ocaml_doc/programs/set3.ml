module type SetSig = sig
   type 'a set
   val empty : 'a set
   val add : 'a -> 'a set -> 'a set
   val mem : 'a -> 'a set -> bool
end;;

module type Set2Sig = sig
   type 'a set
   val empty : 'a set
   val add : 'a set -> 'a -> 'a set
   val mem : 'a -> 'a set -> bool
end;;

module Set : SetSig = struct
   type 'a set = 'a list
   let empty = []
   let add x l = x :: l
   let mem x l = List.mem x l
end;;

module Set2 : Set2Sig =
struct
   include Set
   let add l x = Set.add x l
end;;

module Set2 : Set2Sig with type 'a set = 'a Set.set =
struct
   include Set
   let add l x = Set.add x l
end;;
