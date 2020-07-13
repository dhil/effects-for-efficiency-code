(* MLton compatibility module. *)
structure Cont = struct
   type 'a cont = 'a MLton.Cont.t
   fun callcc f = MLton.Cont.callcc f
   fun throw k v = MLton.Cont.throw(k, v)
end
structure GC = struct
  fun messages v = MLton.GC.setMessages v
end
