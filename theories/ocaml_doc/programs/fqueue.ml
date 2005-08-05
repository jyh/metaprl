type 'a queue = ('a list * 'a list) ref

let empty = ref ([], [])
