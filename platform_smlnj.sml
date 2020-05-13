(* SML/NJ compatibility module. *)
structure Cont = struct
  type 'a cont = 'a SMLofNJ.Cont.cont
  fun callcc f = SMLofNJ.Cont.callcc f
  fun throw k v = SMLofNJ.Cont.throw k v
end
structure GC = struct
  fun messages v = SMLofNJ.Internals.GC.messages v
end

