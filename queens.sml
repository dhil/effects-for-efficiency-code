

(* Comparing solutions to the n queens problem via various
   generic search algorithms and via a bespoke implementation. *)

(* John Longley, started October 2015, tidied up September 2018. *)


(* use "genericSearch.sml" ; *)

(* All our generic search operations take an input of type SearchProblem.
   We here give two ways of presenting n queens as a SearchProblem,
   parametric in n. *)

(* First way: nQueens : int -> SearchProblem *)

(* This doesn't refrain from querying the proposed solution p
   repeatedly on the same argument i.
   E.g. (p 0) is evaluated afresh for each comparison with some (p i), i>0.
   All our generic search implementations are robust enough to cope with this. *)

fun testQueenPair p i j =
    let val (jpos,ipos) = (p j,p i) in
        not (ipos = jpos orelse ipos-jpos = i-j orelse ipos-jpos = j-i)
    end ;

fun testQueenPairsFrom p i j =
    j=i orelse (testQueenPair p i j andalso testQueenPairsFrom p i (j+1)) ;

fun testQueensFrom n p i =
    i=n orelse (testQueenPairsFrom p i 0 andalso testQueensFrom n p (i+1)) ;

fun nQueens n : SearchProblem =
    {dimensions = List.tabulate (n, fn _ => n) ,
     property = fn p => testQueensFrom n p 0} ;

(* Second way: nQueens : int -> SearchProblem *)

(* This remembers results of earlier queries to p, and in fact asks for
   each of p 0, p 1, ... once only, in this order. *)

fun testAgainst y j [] = true
  | testAgainst y j (z::zs) =
    z<>y andalso Int.abs(z-y)<>j andalso testAgainst y (j+1) zs ;

fun testFrom n p i zs =
    if i=n then true
    else let val y = p i
         in  testAgainst y 1 zs andalso testFrom n p (i+1) (y::zs)
         end ;

fun nQueens' n : SearchProblem =
    {dimensions = List.tabulate (n, fn _ => n) ,
     property = fn p => testFrom n p 0 []} ;

(* Efficiency comparisons between nQueens and nQueens' are interesting
   (see below for some typical tests).
   In general, nQueens' is faster, though more dramatically so for some
   generic search algorithms than others.
   In particular, pruned search (without backup) is much more competitive
   for nQueens' than for nQueens.  Advantage of backup is more strikingly
   visible for nQueens. *)


(* BESPOKE implementation of n queens problem, for comparison *)

structure BespokeQueens = struct

local

fun testQueenPair a i j =
    let val (jpos,ipos) = (Array.sub(a,j), Array.sub(a,i)) in
        not (ipos = jpos orelse ipos-jpos = i-j orelse ipos-jpos = j-i)
    end ;

fun testQueenPairsFrom a i j =
    j=i orelse (testQueenPair a i j andalso testQueenPairsFrom a i (j+1)) ;

exception Found of int Array.array ;

fun arrayToList a = Array.foldr (fn (x,l) => x::l) [] a ;

fun searchAllExtensions n a i =
    if i = n then raise Found a
    else searchAllExtensionsFrom n a i 0
and searchAllExtensionsFrom n a i j =
    if j = n then () else
    (Array.update(a,i,j) ;
     if testQueenPairsFrom a i 0
     then searchAllExtensions n a (i+1) else () ;
     searchAllExtensionsFrom n a i (j+1)) ;

fun searchAllExtensions' acc n a i =
    if i = n then arrayToList a :: acc
    else searchAllExtensionsFrom' acc n a i 0
and searchAllExtensionsFrom' acc n a i j =
    if j = n then acc else
    (Array.update(a,i,j) ;
     let val acc' =
         if testQueenPairsFrom a i 0
         then searchAllExtensions' acc n a (i+1)
         else acc
     in searchAllExtensionsFrom' acc' n a i (j+1)
     end) ;

in

fun findOne n =
    (searchAllExtensions n (Array.array(n,0)) 0 ; NONE)
    handle Found a => SOME (arrayToList a) ;

fun findAll n = List.rev (searchAllExtensions' [] n (Array.array(n,0)) 0)

end
end ;


(* For easy testing *)

GC.messages false ;

fun time f x =
    let val timer = Timer.startRealTimer() in
        (f x, Timer.checkRealTimer timer)
    end ;

(* fun naiveOneQ n = time NaiveSearch.findOne (nQueens n) ; *)
(* fun naiveOneQ' n = time NaiveSearch.findOne (nQueens' n) ; *)
(* fun naiveAllQ n = time NaiveSearch.findAll (nQueens n) ; *)
(* fun naiveAllQ' n = time NaiveSearch.findAll (nQueens' n) ; *)

(* fun funOneQ n = time FunSearch.findOne (nQueens n) ; *)
(* fun funOneQ' n = time FunSearch.findOne (nQueens' n) ; *)

(* fun modOneQ n = time ModSearch.findOne (nQueens n) ; *)
(* fun modOneQ' n = time ModSearch.findOne (nQueens' n) ; *)
(* fun modAllQ n = time ModSearch.findAll (nQueens n) ; *)
(* fun modAllQ' n = time ModSearch.findAll (nQueens' n) ; *)

(* fun ccOneQ n = time CcSearch.findOne (nQueens n) ; *)
(* fun ccOneQ' n = time CcSearch.findOne (nQueens' n) ; *)
(* fun ccAllQ n = time CcSearch.findAll (nQueens n) ; *)
(* fun ccAllQ' n = time CcSearch.findAll (nQueens' n) ; *)

(* fun bespokeOneQ n = time BespokeQueens.findOne n ; *)
(* fun bespokeAllQ n = time BespokeQueens.findAll n ; *)

fun naiveOneQ n =  NaiveSearch.findOne (nQueens n) ;
fun naiveOneQ' n =  NaiveSearch.findOne (nQueens' n) ;
fun naiveAllQ n =  NaiveSearch.findAll (nQueens n) ;
fun naiveAllQ' n =  NaiveSearch.findAll (nQueens' n) ;

fun funOneQ n =  FunSearch.findOne (nQueens n) ;
fun funOneQ' n =  FunSearch.findOne (nQueens' n) ;

fun modOneQ n =  ModSearch.findOne (nQueens n) ;
fun modOneQ' n =  ModSearch.findOne (nQueens' n) ;
fun modAllQ n =  ModSearch.findAll (nQueens n) ;
fun modAllQ' n =  ModSearch.findAll (nQueens' n) ;

fun ccOneQ n =  CcSearch.findOne (nQueens n) ;
fun ccOneQ' n =  CcSearch.findOne (nQueens' n) ;
fun ccAllQ n =  CcSearch.findAll (nQueens n) ;
fun ccAllQ' n =  CcSearch.findAll (nQueens' n) ;

fun bespokeOneQ n =  BespokeQueens.findOne n ;
fun bespokeAllQ n =  BespokeQueens.findAll n ;

fun funAllQ n = FunSearch.findAll (nQueens n) ;
fun funAllQ' n = FunSearch.findAll (nQueens' n) ;

(* use "bench.sml"; *)

fun validateAllQ12 xs = List.length xs = 14200
fun validateAllQ10 xs = List.length xs = 724
fun validateAllQ8 xs = List.length xs = 92

fun validateOne12 x = x = SOME [0,2,4,7,9,11,5,10,1,6,8,3]
fun validateOne16 x = x = SOME [0,2,4,1,12,8,13,11,14,5,15,6,3,10,7,9]
fun validateOne20 x = x = SOME [0,2,4,1,3,12,14,11,17,19,16,8,15,18,7,9,6,13,5,10]
fun validateOne24 x = x = SOME [0,2,4,1,3,8,10,13,17,21,18,22,19,23,9,20,5,7,11,15,12,6,16,14]
fun validateOne28 x = x = SOME [0,2,4,1,3,8,10,12,14,16,22,24,21,27,25,23,26,6,11,15,17,7,9,13,19,5,20,18]

exception InvalidArgument

fun validateOne n = case n of
                        12 => validateOne12
                      | 16  => validateOne16
                      | 20 => validateOne20
                      | 24 => validateOne24
                      | 28 => validateOne28
                      | _ => raise InvalidArgument

fun validateAll n = case n of
                        8 => validateAllQ8
                      | 10 => validateAllQ10
                      | 12 => validateAllQ12
                      | _ => raise InvalidArgument

fun tt _ = true

val numIterations = 11
val oneQ : int -> (int list option Bench.t list) = fn n => [
               (* { label = "naive", f = if n > 8 then (fn () => NONE) else (fn () => naiveOneQ n), validate = tt }, *)
               { m = 0, n = n, niter = numIterations, label = "fun", f = if n < 28 then (fn () => funOneQ n) else (fn () => NONE), validate = validateOne n },
               { m = 0, n = n, niter = numIterations, label = "mod", f = (fn () => modOneQ n), validate = validateOne n },
               { m = 0, n = n, niter = numIterations, label = "cc", f = (fn () => ccOneQ n), validate = validateOne n },
               { m = 0, n = n, niter = numIterations, label = "bespoke", f = (fn () => bespokeOneQ n), validate = validateOne n }
           ]

val oneQ' : int -> (int list option Bench.t list) = fn n => [
               (* { label = "naive", f = if n > 8 then (fn () => NONE) else (fn () => naiveOneQ' n), validate = tt }, *)
               { m = 0, n = n, niter = numIterations, label = "funP", f = if n < 28 then (fn () => funOneQ' n) else (fn () => NONE), validate = validateOne n },
               { m = 0, n = n, niter = numIterations, label = "modP", f = (fn () => modOneQ' n), validate = validateOne n },
               { m = 0, n = n, niter = numIterations, label = "ccP", f = (fn () => ccOneQ' n), validate = validateOne n }
               (* { label = "bespoke", f = (fn () => bespokeOneQ n), validate = tt } *)
            ];

val allQ : int -> (int list list Bench.t list) = fn n => [
               { m = 0, n = n, niter = numIterations, label = "naive", f = if n > 8 then (fn () => []) else (fn () => naiveAllQ n), validate = validateAll n },
               { m = 0, n = n, niter = numIterations, label = "mod", f = (fn () => modAllQ n), validate = validateAll n },
               { m = 0, n = n, niter = numIterations, label = "cc", f = (fn () => ccAllQ n), validate = validateAll n },
               { m = 0, n = n, niter = numIterations, label = "bespoke", f = (fn () => bespokeAllQ n), validate = validateAll n },
               { m = 0, n = n, niter = numIterations, label = "fun", f = (fn () => funAllQ n), validate = fn sol => validateAll n (List.rev sol) }
];

val allQ' : int -> (int list list Bench.t list) = fn n => [
               { m = 0, n = n, niter = numIterations, label = "naiveP", f = if n > 8 then (fn () => []) else (fn () => naiveAllQ' n), validate = validateAll n },
               { m = 0, n = n, niter = numIterations, label = "modP", f = (fn () => modAllQ' n), validate = validateAll n },
               { m = 0, n = n, niter = numIterations, label = "ccP", f = (fn () => ccAllQ' n), validate = validateAll n },
               { m = 0, n = n, niter = numIterations, label = "funP", f = (fn () => funAllQ' n), validate = fn sol => validateAll n (List.rev sol) }
               (* { label = "bespoke", f = (fn () => bespokeAllQ n), validate = tt } *)
           ];

fun cartesian ([],        ys) : ('a * 'b) list = []
  | cartesian ((x :: xs), ys) = List.map (fn y => (x, y)) ys @ cartesian (xs, ys)

fun apply (f, x) = f x

val findOneSuite = List.concat (List.map apply (cartesian ([oneQ,oneQ'], [12, 16, 20, 24, 28])))
val findAllSuite = List.concat (List.map apply (cartesian ([allQ,allQ'], [8, 10, 12])))

fun runSuites () =
    let val _ = Bench.runSuite "queens-find-one-sml.csv" findOneSuite
        val _ = Bench.runSuite "queens-find-all-sml.csv" findAllSuite
    in
        ()
    end

structure Test = struct
fun main (progName, args) =
    let val () = runSuites () in
        1
    end
end
(* Some typical results.

Note that the absolute time taken for a given search implementation to find the
first n queens solution will vary erratically with n, as it will depend on
where the first solution happens to lie within the search space.
For 'findOne' experiments, therefore, only the time ratios between different
implementations for the same n are meaningful.

(1) Using nQueens : searchProblem

- naiveAllQ 8 ;
val it =
  ([[0,4,7,5,2,6,1,3],[0,5,7,2,6,3,1,4],[0,6,3,5,7,1,4,2],[0,6,4,7,1,3,5,2],...],
   TIME {usec=2500000}) : int list list * Time.time
- modAllQ 8 ;
val it =
  ([[0,4,7,5,2,6,1,3],[0,5,7,2,6,3,1,4],[0,6,3,5,7,1,4,2],[0,6,4,7,1,3,5,2],...],
   TIME {usec=11000}) : int list list * Time.time
- ccAllQ 8 ;
val it =
  ([[0,4,7,5,2,6,1,3],[0,5,7,2,6,3,1,4],[0,6,3,5,7,1,4,2],[0,6,4,7,1,3,5,2],...],
   TIME {usec=4000}) : int list list * Time.time
- bespokeAllQ 8 ;
val it =
  ([[0,4,7,5,2,6,1,3],[0,5,7,2,6,3,1,4],[0,6,3,5,7,1,4,2],[0,6,4,7,1,3,5,2],...],
   TIME {usec=0}) : int list list * Time.time

- naiveAllQ 10 ;
  (* takes too long *)
- modAllQ 10 ;
val it =
  ([[0,2,5,7,9,4,8,1,3,6],[0,2,5,8,6,9,3,1,4,7],[0,2,5,8,6,9,3,1,7,4],...],
   TIME {usec=366000}) : int list list * Time.time
- ccAllQ 10 ;
val it =
  ([[0,2,5,7,9,4,8,1,3,6],[0,2,5,8,6,9,3,1,4,7],[0,2,5,8,6,9,3,1,7,4],...],
   TIME {usec=115000}) : int list list * Time.time
- bespokeAllQ 10 ;
val it =
  ([[0,2,5,7,9,4,8,1,3,6],[0,2,5,8,6,9,3,1,4,7],[0,2,5,8,6,9,3,1,7,4],...],
   TIME {usec=14000}) : int list list * Time.time
(* Time ratios: cc/bespoke 8.21, mod/cc 3.18 *)

- modAllQ 12 ;
val it =
  ([[0,2,4,7,9,11,5,10,1,6,8,3],[0,2,4,9,7,10,1,11,5,8,6,3],...],
   TIME {usec=14943000}) : int list list * Time.time
- ccAllQ 12 ;
val it =
  ([[0,2,4,7,9,11,5,10,1,6,8,3],[0,2,4,9,7,10,1,11,5,8,6,3],...],
   TIME {usec=3833000}) : int list list * Time.time
- bespokeAllQ 12 ;
val it =
  ([[0,2,4,7,9,11,5,10,1,6,8,3],[0,2,4,9,7,10,1,11,5,8,6,3],...],
   TIME {usec=364000}) : int list list * Time.time
(* Time ratios: cc/bespoke 10.53, mod/cc 3.90 *)

- naiveOneQ 12 ;
  (* too long *)
- funOneQ 12 ;
val it = (SOME [0,2,4,7,9,11,5,10,1,6,8,3],TIME {usec=13000})
- modOneQ 12 ;
val it = (SOME [0,2,4,7,9,11,5,10,1,6,8,3],TIME {usec=4000})
- ccOneQ 12 ;
val it = (SOME [0,2,4,7,9,11,5,10,1,6,8,3],TIME {usec=2000})
- bespokeOneQ 12 ;
val it = (SOME [0,2,4,7,9,11,5,10,1,6,8,3],TIME {usec=0})
(* Time ratios: mod/cc ~2, fun/mod ~3 *)

- funOneQ 16 ;
val it = (SOME [0,2,4,1,12,8,13,11,14,5,15,6,...],TIME {usec=1285000})
- modOneQ 16 ;
val it = (SOME [0,2,4,1,12,8,13,11,14,5,15,6,...],TIME {usec=342000})
- ccOneQ 16 ;
val it = (SOME [0,2,4,1,12,8,13,11,14,5,15,6,...],TIME {usec=68000})
- bespokeOneQ 16 ;
val it = (SOME [0,2,4,1,12,8,13,11,14,5,15,6,...],TIME {usec=6000})
(* Time ratios: cc/bespoke 11.33, mod/cc 5.03, fun/mod 3.76 *)

- funOneQ 20 ;
val it = (SOME [0,2,4,1,3,12,14,11,17,19,16,8,...],TIME {usec=60242000})
- modOneQ 20 ;
val it = (SOME [0,2,4,1,3,12,14,11,17,19,16,8,...],TIME {usec=13193000})
- ccOneQ 20 ;
val it = (SOME [0,2,4,1,3,12,14,11,17,19,16,8,...],TIME {usec=2031000})
- bespokeOneQ 20 ;
val it = (SOME [0,2,4,1,3,12,14,11,17,19,16,8,...],TIME {usec=159000})
(* Time ratios: cc/bespoke 12.77, mod/cc 6.50, fun/mod 4.57 *)

- funOneQ 24 ;
val it = (SOME [0,2,4,1,3,8,10,13,17,21,18,22,...],TIME {usec=250169000})
- modOneQ 24 ;
val it = (SOME [0,2,4,1,3,8,10,13,17,21,18,22,...],TIME {usec=46970000})
- ccOneQ 24 ;
val it = (SOME [0,2,4,1,3,8,10,13,17,21,18,22,...],TIME {usec=5745000})
- bespokeOneQ 24 ;
val it = (SOME [0,2,4,1,3,8,10,13,17,21,18,22,...],TIME {usec=457000})
(* Time ratios: cc/bespoke 12.57, mod/cc 8.18, fun/mod 5.33 *)

- funOneQ 28 ;
  (* too long *)
- modOneQ 28 ;
val it = (SOME [0,2,4,1,3,8,10,12,14,16,22,24,...],TIME {usec=527476000})
- ccOneQ 28 ;
val it = (SOME [0,2,4,1,3,8,10,12,14,16,22,24,...],TIME {usec=55391000})
- bespokeOneQ 28 ;
val it = (SOME [0,2,4,1,3,8,10,12,14,16,22,24,...],TIME {usec=4430000})
(* Time ratios: cc/bespoke 12.50, mod/cc 9.52  *)


(2) Using nQueens' : searchProblem

- funOneQ' 12 ;
val it = (SOME [0,2,4,7,9,11,5,10,1,6,8,3],TIME {usec=7000})
  : int list option * Time.time
- modOneQ' 12 ;
val it = (SOME [0,2,4,7,9,11,5,10,1,6,8,3],TIME {usec=2000})
  : int list option * Time.time
- ccOneQ' 12 ;
val it = (SOME [0,2,4,7,9,11,5,10,1,6,8,3],TIME {usec=0})
  : int list option * Time.time
- bespokeOneQ 12 ;
val it = (SOME [0,2,4,7,9,11,5,10,1,6,8,3],TIME {usec=0})
  : int list option * Time.time
(* Time ratio: fun/mod ~3.5 *)

- funOneQ' 16 ;
val it = (SOME [0,2,4,1,12,8,13,11,14,5,15,6,...],TIME {usec=416000})
  : int list option * Time.time
- modOneQ' 16 ;
val it = (SOME [0,2,4,1,12,8,13,11,14,5,15,6,...],TIME {usec=120000})
  : int list option * Time.time
- ccOneQ' 16 ;
val it = (SOME [0,2,4,1,12,8,13,11,14,5,15,6,...],TIME {usec=55000})
  : int list option * Time.time
- bespokeOneQ 16 ;
val it = (SOME [0,2,4,1,12,8,13,11,14,5,15,6,...],TIME {usec=6000})
  : int list option * Time.time
(* Time ratios: cc/bespoke 9.17, mod/cc 2.18, fun/mod 3.47 *)

- funOneQ' 20 ;
val it = (SOME [0,2,4,1,3,12,14,11,17,19,16,8,...],TIME {usec=17223000})
- modOneQ' 20 ;
val it = (SOME [0,2,4,1,3,12,14,11,17,19,16,8,...],TIME {usec=3795000})
- ccOneQ' 20 ;
val it = (SOME [0,2,4,1,3,12,14,11,17,19,16,8,...],TIME {usec=1648000})
- bespokeOneQ 20 ;
val it = (SOME [0,2,4,1,3,12,14,11,17,19,16,8,...],TIME {usec=158000})
(* Time ratios: cc/bespoke 10.43, mod/cc 2.30, fun/mod 4.54 *)

- funOneQ' 24 ;
val it = (SOME [0,2,4,1,3,8,10,13,17,21,18,22,...],TIME {usec=65303000})
- modOneQ' 24 ;
val it = (SOME [0,2,4,1,3,8,10,13,17,21,18,22,...],TIME {usec=12193000})
- ccOneQ' 24 ;
val it = (SOME [0,2,4,1,3,8,10,13,17,21,18,22,...],TIME {usec=4567000})
- bespokeOneQ 24 ;
val it = (SOME [0,2,4,1,3,8,10,13,17,21,18,22,...],TIME {usec=461000})
(* Time ratios: cc/bespoke 9.90, mod/cc 2.67, fun/mod 5.36 *)

- funOneQ' 28 ;
  (* too long *)
- modOneQ' 28 ;
val it = (SOME [0,2,4,1,3,8,10,12,14,16,22,24,...],TIME {usec=129494000})
- ccOneQ' 28 ;
val it = (SOME [0,2,4,1,3,8,10,12,14,16,22,24,...],TIME {usec=43511000})
- bespokeOneQ 28 ;
val it = (SOME [0,2,4,1,3,8,10,12,14,16,22,24,...],TIME {usec=4390000})
(* Time ratios: cc/bespoke 9.91, mod/cc 2.98 *)

*)
