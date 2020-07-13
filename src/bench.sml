structure Bench =
struct
type 'a t = {
    m: int,
    n: int,
    niter: int,
    label: string,
    f: unit -> 'a,
    validate: 'a -> bool
};

fun to_csv label i n elapsed valid =
    label ^ "," ^ (Int.toString i) ^ "," ^ (Int.toString n) ^ "," ^ (LargeInt.toString elapsed) ^ "," ^ valid ^ "\n"

fun get_usec {usec=u, sec=s} = u

fun run oc r =
    let fun loop (r : 'a t) i n =
            if i < n then
                let val s = (Int.toString (i+1)) ^ "/" ^ (Int.toString n) ^ " Running " ^ (#label r) ^ "..."
                    val () = print s
                    val t = Timer.startRealTimer()
                    val result = (#f r) ()
                    val elapsed = Time.toMicroseconds (Timer.checkRealTimer t)
                    val valid = (#validate r) result
                    val label = (#label r)
                in
                    (if valid then
                         print " SUCCESS!\n"
                     else
                         print " FAILURE!\n");
                    TextIO.output (oc, to_csv label (i+1) (#n r) elapsed (if valid then "true" else "false"));
                    TextIO.flushOut oc;
                    loop r (i + 1) n
                end
            else ()
    in
        loop r 0 (#niter r)
    end

fun runSuite logfile (items : 'a t list) =
    let val oc = TextIO.openOut logfile
        val () = TextIO.output (oc, "label,iter,n,elapsed,valid\n")
        val () = TextIO.flushOut oc
        val n = List.length items
        fun for oc i [] = ()
          | for oc i (x :: xs) =
            let val () = print ("Starting benchmark [" ^ (Int.toString i) ^ "/" ^ (Int.toString n) ^ "]...\n")
            in run oc x; for oc (i+1) xs
            end
    in
        for oc 1 items;
        TextIO.closeOut oc
    end
end
