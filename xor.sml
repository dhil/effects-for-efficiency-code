use "genericSearch.sml";

exception InvalidArgument

fun xor 1 0 = 1
  | xor 0 1 = 1
  | xor 0 0 = 0
  | xor 1 1 = 0
  | xor _ _ = raise InvalidArgument;

fun odd n (p : int -> int) =
    let fun coerce 1 = true
          | coerce 0 = false
          | coerce _ = raise InvalidArgument
        fun loop p acc i n =
            if i < n then loop p (xor (p i) acc) (i + 1) n
            else acc
    in coerce (loop p 0 0 n)
    end;

fun oddProp n : SearchProblem =
    { dimensions = List.tabulate (n, fn _ => 2),
      property = odd n } ;

(* For easy testing *)

SMLofNJ.Internals.GC.messages false ;

fun time f x =
    let val timer = Timer.startRealTimer() in
        (f x, Timer.checkRealTimer timer)
    end ;

fun naiveX n = NaiveSearch.findAll (oddProp n) ;
fun funX n = FunSearch.findAll (oddProp n) ;
fun modX n = ModSearch.findAll (oddProp n) ;
fun ccX n = CcSearch.findAll (oddProp n) ;

use "bench.sml";

fun tt _ = true
val numIterations = 11
val allX : int -> (int list list Bench.t list) = fn n => [
          { m = 0, n = n, niter = numIterations, label = "naive", f = (fn () => naiveX n), validate = tt },
          { m = 0, n = n, niter = numIterations, label = "fun", f = (fn () => funX n), validate = tt },
          { m = 0, n = n, niter = numIterations, label = "mod", f = (fn () => modX n), validate = tt },
          { m = 0, n = n, niter = numIterations, label = "cc", f = (fn () => ccX n), validate = tt } ] ;

fun cartesian ([],        ys) : ('a * 'b) list = []
  | cartesian ((x :: xs), ys) = List.map (fn y => (x, y)) ys @ cartesian (xs, ys)

fun apply (f, x) = f x

val allXSuite = List.concat (List.map apply (cartesian ([allX], [16, 18, 20])))

fun runSuites () =
    let val _ = Bench.runSuite "odd-all-sml.csv" allXSuite
    in
        ()
    end

structure Test = struct
fun main (progName, args) =
    let val () = runSuites () in
        1
    end
end


