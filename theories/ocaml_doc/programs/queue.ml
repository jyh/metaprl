type 'a elem = 'a * 'a pointer
and 'a pointer = Pointer of 'a elem ref
type 'a queue = 'a elem option ref

let create () =
   None

let enqueue queue x =
   match !queue with
      Some (_, Pointer oldest_ref) ->
         let oldest = !oldest_ref in
         let current = (x, Pointer (ref oldest)) in
            oldest_ref := current;
            queue := Some current
    | None ->
         let rec current = (x, Pointer (ref current)) in
             queue := Some current

  let dequeue queue =
      match !queue with
         None ->
            (* The queue is empty *)
            raise Not_found
       | Some (_, Pointer oldest_ref) ->
            let oldest = !oldest_ref in
            let (x, Pointer next_ref) = oldest in
            let next = !next_ref in
               if next == oldest then
                  (* The oldest element points to itself *)
                  queue := None
               else
                  (* Unlink the oldest from the queue *)
                  oldest_ref := next;
               x
