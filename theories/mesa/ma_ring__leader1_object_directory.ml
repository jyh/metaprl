extends Nuprl_ring__leader1_object_directory

(*
let repeatWithRwsT tac defs  = repeatT (firstT (map (fun def-> progressT (rwh def 0) thenT tac ) defs))

let auto_and_dT =  onAllHypsT (fun n-> (tryT (completeT (dT n ta))))


let superT defs = repeatT (firstT (map (fun def-> progressT (rwh def 0) ta ) defs))  thenT onAllHypsT (fun n-> (tryT (completeT (dT n thenT autoT))))

*)
