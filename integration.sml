
(* Efficiency comparisons for various exact real integration operators,
   including one using catchcont. *)

(* John Longley, September 2018 (drawing on much earlier attempts) *)


(* We use int streams with digits 1,0,~1 to represent reals in [-1,1].
So (int stream -> int stream) represents math functions [-1,1] -> [-1,1].

We give four integration functions of the form:
   ...Integrate01 : int -> (int stream -> int stream) -> dyadic
which perform definite integration from 0 to 1 with any specified precision.
More precisely, if F : int stream -> int stream represents f : [-1,1] -> [-1,1],
then ...Integrate01 k F returns some dyadic within 2^-k of the true value
of the integral of f from 0 to 1.

In fact, for any given k and F, all four of our integrators will return the
*same* dyadic approximation - they are all accessing the same information
about F - so that efficiency comparisons between them are indeed meaningful. *)


use "catchcont.sml" ;

(* Big integers *)

type big = IntInf.int ;
val toBig = IntInf.fromInt ;
val toSmall = IntInf.toInt ;

(* type big = int ; *)
(* val toBig = fn x => x ; *)
(* val toSmall = fn x => x ; *)

fun printSmall n = print (Int.toString n ^ " ") ;


(* Memoized powers of two *)

val maxTwoExponent = 80 ;

val twoToArray = Array.array (maxTwoExponent, 0:big) ;

fun fillTwoToArray i twoToi =
    if i=maxTwoExponent then ()
    else (Array.update(twoToArray,i,twoToi) ;
          fillTwoToArray (i+1) (twoToi*2)) ;
fillTwoToArray 0 1 ;

fun twoTo i = Array.sub (twoToArray, i) ;


(* Basic dyadic arithmetic *)

type dyadic = big * int ;   (* (a,k) represents a*2^k *)

val dyZero:dyadic = (0,~1) ;
val dyOne:dyadic  = (1,0) ;
val dyHalf:dyadic = (1,~1) ;
val dyMinusHalf:dyadic = (~1,~1) ;

fun simp ((a,k):dyadic) : dyadic =
    case a mod 4 of
       0 => if a=0 then dyZero else simp (a div 4, k+2)
     | 2 => (a div 2, k+1)
     | _ => (a,k) ;

fun add ((a,k):dyadic) ((a',k'):dyadic) =
    if k >= k' then (twoTo(k-k')*a + a', k')
    else (a + twoTo(k'-k)*a', k) ;
    (* better not to simplify result, it seems *)

fun neg ((a,k):dyadic) : dyadic = (~a,k) ;

fun sub d d' = add d (neg d') ;

fun mult ((a,k):dyadic) ((a',k'):dyadic) = (a*a', k+k') ;
    (* better not to simplify *)

fun leq ((a,k):dyadic) ((a',k'):dyadic) =
    if k >= k' then twoTo(k-k')*a <= a' else a <= twoTo(k'-k)*a' ;

fun rescale ((a,k):dyadic) k' = ((a,k+k'):dyadic) ;

fun average d d' = rescale (add d d') ~1 ;

local fun thrice ((a,k):dyadic) = (a+a+a,k) in
fun leftAverage d d' = rescale (add (thrice d) d') ~2 ;   (* (3d+d')/4 *)
fun rightAverage d d' = rescale (add d (thrice d')) ~2    (* (d+3d')/4 *)
end ;

fun printDyadic ((a,k):dyadic) =
    print ("(" ^ IntInf.toString a ^ "," ^ Int.toString k ^ ") ") ;


(* Signed binary streams, representing reals in [~1,1]. Digits are 1,0,~1. *)

datatype 'a stream = Cons of 'a * (unit -> 'a stream) ;

fun tail (Cons (x,u)) = u() ;

fun constStream d = Cons (d, fn () => constStream d) ;

fun append [] s = s
  | append (d::ds) s = Cons (d, fn () => append ds s) ;

fun bigToStream m j =
    (* Produces stream rep of integer m in [-2^j,2^j), relative to [-2^j,2^j].
       Will consist of just ~1 and 1, ending in an infinite tail of ~1s.
       First j+1 digits will be the binary rep of m+2^j, writing ~1 for 0. *)
    if j=0 then (if m = ~1 then constStream ~1
                 else Cons (1, fn () => constStream ~1))
    else case j-1 of j' =>
         if m < 0 then Cons (~1, fn () => bigToStream (m + twoTo j') j')
	 else Cons (1, fn () => bigToStream (m - twoTo j') j') ;

fun dyadicToStream (a,k) = bigToStream a (~k) ;
    (* Produces signed binary stream for dyadic in range [~1,1),
       consisting of just ~1 and 1 and ending in tail of ~1.
       This choice of representation facilitates comparison with the
       catchcont implementation of integration. *)

fun digitListToDyadic i [] = dyZero
  | digitListToDyadic i (d::ds) =
    add (toBig d, i) (digitListToDyadic (i-1) ds) ;
    (* returns centre of interval represented by a finite digit list *)

fun takeDigits 0 str = []
  | takeDigits 1 (Cons(x,u)) = [x]
  | takeDigits i (Cons(x,u)) = x :: takeDigits (i-1) (u()) ;

fun streamToDyadic k str = digitListToDyadic ~1 (takeDigits k str) ;
    (* returns a dyadic within 2^-k of the true value of str *)

fun applyToPrecision k F str = streamToDyadic k (F str) ;

fun digitListToMaxDyadic i [] = (1,i+1)
  | digitListToMaxDyadic i (d::ds) =
    add (toBig d, i) (digitListToMaxDyadic (i-1) ds) ;
    (* returns right end of interval represented by a finite digit list *)


(* INTEGRATION OPERATIONS *)

(* Purely functional integration (Berger/Simpson) *)

(* We allow stream memoization to achieve the typical effect of
   a Haskell-style call-by-need implementation - we consider this
   to be within the spirit of 'pure functional' programming.
*)

fun addToVector ds d = Vector.concat [ds, Vector.fromList [d]] ;

fun memoStream' i memo =
    case !memo of (ds,u) =>
        if i < Vector.length ds
	then Cons (Vector.sub(ds,i), fn () => memoStream' (i+1) memo)
        else case u() of Cons(d,u') =>
	     (memo := (addToVector ds d, u') ;
	      Cons (d, fn () => memoStream' (i+1) memo)) ;

fun memoStream (Cons(d,u)) =
    let val memo = ref (Vector.fromList [d], u)
    in  memoStream' 0 memo
    end ;

fun criticalStream G (Y:dyadic) ds =
    let val s = memoStream (Cons (~1, fn () => criticalStream G Y (ds @ [~1])))
    in  if G (append ds s) <> Y then s
        else Cons (1, fn () => criticalStream G Y (ds @ [1]))
    end ;

fun funIntegrate' G ds Z =
    let val Y = case Z of SOME Y' => Y'
                        | NONE => G (append ds (constStream ~1))
    in  if G (append ds (criticalStream G Y ds)) = Y
        then rescale Y (1 - List.length ds)
        else add (funIntegrate' G (ds @ [~1]) Z)
	         (* passing Z here saves recomputing G (ds @ ~1,~1,~1,...) *)
	         (funIntegrate' G (ds @ [1]) NONE)
    end ;

fun funIntegrate01 k F = simp (funIntegrate' (applyToPrecision k F) [1] NONE) ;


(* Slower version omitting memoization, for comparison: *)

fun slowCriticalStream G (Y:dyadic) ds =
    let val s = Cons (~1, fn () => slowCriticalStream G Y (ds @ [~1]))
    in  if G (append ds s) <> Y then s
        else Cons (1, fn () => slowCriticalStream G Y (ds @ [1]))
    end ;

fun slowFunIntegrate' G ds Z =
    let val Y = case Z of SOME Y' => Y'
                        | NONE => G (append ds (constStream ~1))
    in  if G (append ds (slowCriticalStream G Y ds)) = Y
        then rescale Y (1 - List.length ds)
        else add (slowFunIntegrate' G (ds @ [~1]) Z)
	         (* passing Z here saves recomputing G (ds @ ~1,~1,~1,...) *)
	         (slowFunIntegrate' G (ds @ [1]) NONE)
    end ;

fun slowFunIntegrate01 k F =
    simp (slowFunIntegrate' (applyToPrecision k F) [1] NONE) ;


(* Stream modulus functional, implemented using local state.
   Example of a sequentially realizable functional. *)

fun resultWithModulus F str =
    (* returns value of F str, plus the portion of str used to obtain this *)
    let val log = ref ([] : int list) ;
        fun logStream (Cons(x,u)) =
	    (log := x :: !log ;
	     Cons (x, fn () => logStream (u()))) ;
	val result = F (logStream str)
    in (result, List.rev (!log))
    end ;

(* Integration using modulus functional *)

fun eqOne (a,k) = (a = twoTo(~k)) ;

fun modIntegrate k F start =
    (* integrates F from start up to 1, with precision k *)
    let fun sweep X total =
	    if eqOne X then total
	    else let val (Y, modulus) =
	             resultWithModulus (applyToPrecision k F)
		                       (dyadicToStream X) ;
		     val newX = digitListToMaxDyadic ~1 modulus
		 in  sweep newX (add total (mult Y (sub newX X)))
		 end 
    in
        sweep start dyZero
    end ;

fun modIntegrate01 k F = simp (modIntegrate k F dyZero) ;

(* Integration using catchcont *)

exception NonLinear ;

fun ccIntegrate' i (G: (unit -> int stream) -> dyadic) =
    case Catchcont.catchcont0 G of
    (* 'r = unit, 's = int stream, 't = dyadic *)
        inl answer => rescale (#result answer) i
      | inr cont =>
            add (ccIntegrate' (i-1)
                 (fn g : unit -> int stream =>
		     (#resume cont) (Cons(~1,g)) (fn _ => raise NonLinear)))
		(ccIntegrate' (i-1)
                 (fn g : unit -> int stream =>
		     (#resume cont) (Cons(1,g)) (fn _ => raise NonLinear))) ;

fun ccIntegrate01 k F =
    simp (ccIntegrate' 0 (fn g: unit -> int stream =>
                                applyToPrecision k F (Cons (1,g)))) ;


(* Example: Squaring *)

exception SquareError ;

fun sqStream' inWt outWt sqmin sqmax u =
    if leq dyZero sqmin then
       Cons (1, fn () => sqStream' inWt (outWt-1)
                 (sub (rescale sqmin 1) dyOne) (sub (rescale sqmax 1) dyOne) u)
    else if leq sqmax dyZero then
       Cons (~1, fn () => sqStream' inWt (outWt-1)
                 (add (rescale sqmin 1) dyOne) (add (rescale sqmax 1) dyOne) u)
    else if leq dyMinusHalf sqmin andalso leq sqmax dyHalf then
       Cons (0, fn () => sqStream' inWt (outWt-1)
                 (rescale sqmin 1) (rescale sqmax 1) u)
    else (case u() of
       Cons (1,u') => sqStream' (inWt-1) outWt
                      (sub (average sqmin sqmax) (1, 2*inWt-outWt))
		      sqmax
		      u'
     | Cons (~1,u') => sqStream' (inWt-1) outWt
                      sqmin
		      (sub (average sqmin sqmax) (1, 2*inWt-outWt))
                      u'
     | Cons (0,u') => sqStream' (inWt-1) outWt
                      (sub (leftAverage sqmin sqmax) (3, 2*inWt-2-outWt))
		      (sub (rightAverage sqmin sqmax) (3, 2*inWt-2-outWt))
                      u'
     | _ => raise SquareError) ;

fun negStream (Cons (d,u)) = Cons (~d, fn () => negStream (u())) ;

fun square (Cons (1,u)) = sqStream' ~1 0 dyZero dyOne u
  | square (Cons (~1,u)) = sqStream' ~1 0 dyZero dyOne (negStream o u)
  | square (Cons (0,u)) = Cons (0, fn () => Cons (0, square o u))
  | square _ = raise SquareError ;


(* Logistic map: x -> 1 - 2x^2. Iterations of this behave chaotically. *)

fun logistic s = case square s of Cons (_,u) => negStream (u()) ;

fun iter 0 f x = x
  | iter n f x = iter (n-1) f (f x) ;

fun id x = x ;



(* For timing experiments: *)

fun time2 f x y =
    let val T = Timer.startRealTimer() in
        (f x y, Timer.checkRealTimer T)
    end ;

fun tt x = true;

use "bench.sml";

exception InvalidArgument

fun validateId20 (x : dyadic) = x = (1, ~1)
fun validateSquare14 (x : dyadic) = x = (44739467,~27)
fun validateSquare17 (x : dyadic) = x = (2863312299,~33)
fun validateSquare20 (x : dyadic) = x = (183251940523,~39)

fun validateFun (fname, n) = case fname of
                                 "id" => if n = 20 then validateId20
                                         else raise InvalidArgument
                               | "square" => (case n of
                                                  14 => validateSquare14
                                                | 17 => validateSquare17
                                                | 20 => validateSquare20
                                                | _  => raise InvalidArgument)
                               | _ => raise InvalidArgument

fun funToIntegrate fname = case fname of
                               "id" => id
                             | "square" => square
                             | _ => raise InvalidArgument

val numIterations = 11
val integrationFuns : (string * int) -> (dyadic Bench.t list)
    = fn (f, n) => [(* { m = 0, n = n, niter = numIterations, label = "slowFun", f = let val g = funToIntegrate f in (fn () => slowFunIntegrate01 n g) end, validate = validateFun (f, n) }, *)
                    { m = 0, n = n, niter = numIterations, label = "fun", f = let val g = funToIntegrate f in (fn () => funIntegrate01 n g) end, validate = validateFun (f, n) },
                    { m = 0, n = n, niter = numIterations, label = "mod", f = let val g = funToIntegrate f in (fn () => modIntegrate01 n g) end, validate = validateFun (f, n) },
                    { m = 0, n = n, niter = numIterations, label = "cc", f = let val g = funToIntegrate f in (fn () => ccIntegrate01 n g) end, validate = validateFun (f, n) }]

fun cartesian ([],        ys) : ('a * 'b) list = []
  | cartesian ((x :: xs), ys) = List.map (fn y => (x, y)) ys @ cartesian (xs, ys)

val typicalId = List.concat (List.map (fn (f, arg) => f arg) (cartesian ([integrationFuns], [("id", 20)])))
val typicalSquare = List.concat (List.map (fn (f, arg) => f arg) (cartesian ([integrationFuns], [("square", 14), ("square", 17), ("square", 20)])))

fun validateLogisticFun (m, n) : (dyadic -> bool)
    = case m of
          15 => (case n of
                     1 => (fn x => x = (357913429,~30))
                   | 2 => (fn x => x = (~6299289887,~35))
                   | 3 => (fn x => x = (~9360359951,~36))
                   | 4 => (fn x => x = (~42633981081,~40))
                   | 5 => (fn x => x = (~16548145409,~40))
                   | _ => raise InvalidArgument)
        | 10 => (case n of
                     8 => (fn x => x = (~13383190727,~41))
                       | _ => raise InvalidArgument)
        |  5 => (case n of
                     10 => (fn x => x = (~6233913477,~38))
                   | 8 => (fn x => x = (~48867099,~31))
                   | _ => raise InvalidArgument)
        | _ => raise InvalidArgument


val logistic' : (int * int) -> (dyadic Bench.t list)
    = fn (m, n) => [
          { m = m, n = n, niter = numIterations, label = "fun", f = (fn () => funIntegrate01 m (iter n logistic)), validate = validateLogisticFun (m, n) },
          { m = m, n = n, niter = numIterations, label = "mod", f = (fn () => modIntegrate01 m (iter n logistic)), validate = validateLogisticFun (m, n) },
          { m = m, n = n, niter = numIterations, label = "cc", f = (fn () => ccIntegrate01 m (iter n logistic)), validate = validateLogisticFun (m, n) }
      ]

val logisticSuite = List.concat (List.map (fn (f, arg) => f arg) (cartesian ([logistic'], [(15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (5, 8), (10, 8), (5, 10)])))

structure Test = struct
  fun main (progName, args) =
      let val () = Bench.runSuite "integration-id-sml.csv" typicalId
          val () = Bench.runSuite "integration-square-sml.csv" typicalSquare
          val () = Bench.runSuite "integration-logistic-sml.csv" logisticSuite
      in
          1
      end
end


(* (* Typical tests: *)

(* Identity function: not representative, but
   cc implementation still gives some speedup. *)

- time2 slowFunIntegrate01 20 id ;
val it = ((1,~1),TIME {usec=23738000}) : dyadic * Time.time
- time2 funIntegrate01 20 id ;
val it = ((1,~1),TIME {usec=7597000}) : dyadic * Time.time
- time2 modIntegrate01 20 id ;
val it = ((1,~1),TIME {usec=2870000}) : dyadic * Time.time
- time2 ccIntegrate01 20 id ;
val it = ((1,~1),TIME {usec=1343000}) : dyadic * Time.time
(* Time ratios: mod/cc 2.14, fun/mod 2.65, slowFun/fun 3.12 *)

(* Squaring function: effect of varying precision *)

- time2 slowFunIntegrate01 14 square ;
val it = ((44739467,~27),TIME {usec=2647000}) : dyadic * Time.time
- time2 funIntegrate01 14 square ;
val it = ((44739467,~27),TIME {usec=1228000}) : dyadic * Time.time
- time2 modIntegrate01 14 square ;
val it = ((44739467,~27),TIME {usec=221000}) : dyadic * Time.time
- time2 ccIntegrate01 14 square ;
val it = ((44739467,~27),TIME {usec=51000}) : dyadic * Time.time
(* Time ratios: mod/cc 4.33, fun/mod 5.56, slowFun/fun 2.16 *)

- time2 slowFunIntegrate01 17 square ;
val it = ((2863312299,~33),TIME {usec=30841000}) : dyadic * Time.time
- time2 funIntegrate01 17 square ;
val it = ((2863312299,~33),TIME {usec=12043000}) : dyadic * Time.time
- time2 modIntegrate01 17 square ;
val it = ((2863312299,~33),TIME {usec=2160000}) : dyadic * Time.time
- time2 ccIntegrate01 17 square ;
val it = ((2863312299,~33),TIME {usec=450000}) : dyadic * Time.time
(* Time ratios: mod/cc 4.80, fun/mod 5.58, slowFun/fun 2.56 *)

- time2 slowFunIntegrate01 20 square ;
val it = ((183251940523,~39),TIME {usec=337489000}) : dyadic * Time.time
- time2 funIntegrate01 20 square ;
val it = ((183251940523,~39),TIME {usec=113627000}) : dyadic * Time.time
- time2 modIntegrate01 20 square ;
val it = ((183251940523,~39),TIME {usec=20208000}) : dyadic * Time.time
- time2 ccIntegrate01 20 square ;
val it = ((183251940523,~39),TIME {usec=3961000}) : dyadic * Time.time
(* Time ratios: mod/cc 5.10, fun/mod 5.62, slowFun/fun 2.97 *)

(* Effect of fixing precision but making function harder to compute:
   iterations of logistic map with precision 15 *)

- time2 ccIntegrate01 15 (iter 1 logistic) ;
val it = ((357913429,~30),TIME {usec=213000}) : dyadic * Time.time
- time2 modIntegrate01 15 (iter 1 logistic) ;
val it = ((357913429,~30),TIME {usec=996000}) : dyadic * Time.time
(* Time ratio: 4.68 *)

- time2 ccIntegrate01 15 (iter 2 logistic) ;
val it = ((~6299289887,~35),TIME {usec=1315000}) : dyadic * Time.time
- time2 modIntegrate01 15 (iter 2 logistic) ;
val it = ((~6299289887,~35),TIME {usec=7985000}) : dyadic * Time.time
(* Time ratio: 6.07 *)

- time2 ccIntegrate01 15 (iter 3 logistic) ;
val it = ((~9360359951,~36),TIME {usec=5842000}) : dyadic * Time.time
- time2 modIntegrate01 15 (iter 3 logistic) ;
val it = ((~9360359951,~36),TIME {usec=42208000}) : dyadic * Time.time
(* Time ratio: 7.22 *)

- time2 ccIntegrate01 15 (iter 4 logistic) ;
val it = ((~42633981081,~40),TIME {usec=22947000}) : dyadic * Time.time
- time2 modIntegrate01 15 (iter 4 logistic) ;
val it = ((~42633981081,~40),TIME {usec=184035000}) : dyadic * Time.time
(* Time ratio: 8.02 *)

- time2 ccIntegrate01 15 (iter 5 logistic) ;
val it = ((~16548145409,~40),TIME {usec=78497000}) : dyadic * Time.time
- time2 modIntegrate01 15 (iter 5 logistic) ;
val it = ((~16548145409,~40),TIME {usec=694657000}) : dyadic * Time.time
(* Time ratio: 8.84 *)

(* Even more iterations but less precision: *)

- time2 ccIntegrate01 5 (iter 8 logistic) ;
val it = ((~48867099,~31),TIME {usec=1727000}) : dyadic * Time.time
- time2 modIntegrate01 5 (iter 8 logistic) ;
(* Time ratio: 6.97 *)
- time2 ccIntegrate01 10 (iter 8 logistic) ;
val it = ((~13383190727,~41),TIME {usec=65662000}) : dyadic * Time.time
- time2 modIntegrate01 10 (iter 8 logistic) ;
val it = ((~13383190727,~41),TIME {usec=588890000}) : dyadic * Time.time
(* Time ratio: 8.97 *)

- time2 ccIntegrate01 5 (iter 10 logistic) ;
val it = ((~6233913477,~38),TIME {usec=13332000}) : dyadic * Time.time
- time2 modIntegrate01 5 (iter 10 logistic) ;
val it = ((~6233913477,~38),TIME {usec=106524000}) : dyadic * Time.time
(* Time ratio: 7.99 *)

*)
