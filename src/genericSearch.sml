

(* NJ-SML implementations of some generic search algorithms,
   including one using 'catchcont'. *)

(* John Longley, started October 2015, tidied up September 2018. *)

(* We give four implementations of generic search using different methods
   and language features, all cast as instances of a signature GENERIC_SEARCH.
   Search spaces are hypercuboids of any dimension: e.g. the list [3,4,5,6]
   specifies the space of points (x0,x1,x2,x3) where the xi are natural numbers
   and x0<3, x1<4, x2<5, x3<6 (a space of size 3x4x5x6).
   Points themselves are represented by functions p : int->int
   (e.g. p i = xi for i=0,1,2,3).
*)


type SearchProblem = {dimensions : int list, property : (int->int)->bool} ;

signature GENERIC_SEARCH = sig
    val findOne : SearchProblem -> int list option
    val findAll : SearchProblem -> int list list
end ;


(* Naive exhaustive search done generically.
   Not remotely competitive, but included here for completeness. *)

structure NaiveSearch : GENERIC_SEARCH = struct

exception Finished ;

fun nextPoint' maxs coords i =
    if Array.sub(coords,i) < Array.sub(maxs,i)
    then (Array.update(coords,i,Array.sub(coords,i)+1) ; coords)
    else if i>0 then (Array.update(coords,i,0) ; nextPoint' maxs coords (i-1))
    else raise Finished ;

fun nextPoint maxs coords = nextPoint' maxs coords (Array.length coords - 1) ;

fun nextPoint1 maxs coords =
    SOME (nextPoint maxs coords) handle Finished => NONE ;

fun arrayToList a = Array.foldr (fn (x,l) => x::l) [] a ;

fun findOne' property maxs coords =
    (if property (fn i => Array.sub(coords,i))
    then SOME (arrayToList coords)
    else findOne' property maxs (nextPoint maxs coords)) ;

fun findAll' property maxs coords =
    (if property (fn i => Array.sub(coords,i))
    then (arrayToList coords) :: findAll' property maxs (nextPoint maxs coords)
    else findAll'' property maxs (nextPoint1 maxs coords))
and findAll'' property maxs (SOME coords) = findAll' property maxs coords
  | findAll'' property maxs NONE = [] ;

exception EmptySpace ;

fun decrement n = if n>0 then n-1 else raise EmptySpace ; (* fussy? *)

fun startSearch searchOp default (prob:SearchProblem) =
    (searchOp (#property prob)
              (Array.fromList (map decrement (#dimensions prob)))
              (Array.array ((List.length(#dimensions prob), 0))))
    handle EmptySpace => default | Finished => default ;

fun findOne (prob:SearchProblem) = startSearch findOne' NONE prob ;
fun findAll (prob:SearchProblem) = startSearch findAll' [] prob ;

end (* struct *) ;



(* 'Pure functional' implementation of findOne using Berger's algorithm. *)
(* Version with vectors: no in-place update. *)
(* NB findAll not currently implemented *)

structure FunSearch : GENERIC_SEARCH = struct

    (* 'Functional' version with vectors: no in-place update *)

    open Vector ;

    (* Memoization operation, to achieve effect of call-by-need.
       Observationally equivalent to identity, so morally functional. *)

    fun memoize (thunk : unit -> 'a) =
        let val cache = ref (NONE : 'a option) in
	    fn () => case !cache of
	        SOME x => x
	      | NONE => let val x = thunk() in
	                    (cache := SOME x) ; x
			end
        end ;

    (* Berger's algorithm: selection function for a property P *)

(* Original version of select, with bestShot/bestFun localized:

    fun select P allDims =
        let val lgth = List.length allDims ;
	    fun bestShot fullSol [] _ = fullSol
              | bestShot partSol (d::dims) i =
                let val partSol' = concat [partSol, fromList[i]]
                in  if i = d-1
	            then bestShot partSol' dims 0
                    else let val f = bestFun partSol' dims
	                 in if P f then tabulate (lgth, f)
	                     else bestShot partSol (d::dims) (i+1)
	                 end
                end
            and bestFun partSol dims =
                let val fallback = memoize (fn () => bestShot partSol dims 0)
	        in  fn i => if i < length partSol then sub (partSol, i)
 	                    else sub (fallback(), i)
                end
        in  bestShot (fromList []) allDims 0
	end ;

*)

(* Select function now restructured to expose bestFun (called by findAll): *)

    fun bestShot P lgth fullSol [] _ = fullSol
      | bestShot P lgth partSol (d::dims) i =
       	let val partSol' = concat [partSol, fromList[i]]
        in  if i = d-1
	    then bestShot P lgth partSol' dims 0
            else let val f = bestFun P lgth partSol' dims
	         in if P f then tabulate (lgth, f)
	            else bestShot P lgth partSol (d::dims) (i+1)
	         end
        end

    and bestFun P lgth partSol dims =
        let val fallback = memoize (fn () => bestShot P lgth partSol dims 0)
	in  fn i => if i < length partSol then sub (partSol, i)
 	            else sub (fallback(), i)
        end

    fun select P allDims =
        let val lgth = List.length allDims ;
        in  bestShot P lgth (fromList []) allDims 0
	end ;


(* Alt version with fixed-length vectors: currently slightly slower.
   Not currently used. *)

    fun select' P allDims =
        let val lgth = List.length allDims ;
	    fun bestShot fullSol pos [] _ = fullSol
              | bestShot partSol pos (d::dims) i =
                let val partSol' = update (partSol,pos,i)
                in  if i = d-1
	            then bestShot partSol' (pos+1) dims 0
                    else let val f = bestFun partSol' (pos+1) dims
	                 in if P f then tabulate (lgth, f)
	                     else bestShot partSol pos (d::dims) (i+1)
	                 end
                end
            and bestFun partSol pos dims =
                let val fallback = memoize (fn () => bestShot partSol pos dims 0)
	        in  fn i => if i < pos then sub (partSol, i)
 	                    else sub (fallback(), i)
                end
        in  bestShot (tabulate (lgth, fn _ => 0)) 0 allDims 0
	end ;

(* Back to main code: *)

    fun vectorToList v = foldr List.:: [] v ;

    fun findOne (prob:SearchProblem) =
        let val P = #property prob
	    val best = select P (#dimensions prob)
	in  if P (fn i => sub(best,i)) then SOME (vectorToList best)
	    else NONE
        end

(* New code: *)

    fun findAll (prob:SearchProblem) =
        let val P = #property prob
	    val alldims = #dimensions prob
	    val lgth = List.length alldims

	    (* find all solutions in fresh subtree determined by partSol: *)
	    fun findAll' partSol pos [] acc = (* 'partial' sol is full here *)
	        if P (fn i => sub(partSol,i))
		then (vectorToList partSol)::acc
		else acc
              | findAll' partSol pos remDims acc =
                let val f = bestFun P lgth partSol remDims
	        in  if P f
	            then findAll'' partSol pos remDims (tabulate (lgth, f)) acc
                    else acc
	        end

	    (* find all solutions in already searched subtree det by partSol,
	       given that fullSol is the leftmost full solution: *)
	    and findAll'' partSol pos [] fullSol acc =
	        (vectorToList fullSol)::acc
              | findAll'' partSol pos (d::dims) fullSol acc =
                let val i = sub (fullSol, pos)
	            val acc' = findAll'' (concat [partSol, fromList[i]])
	                                 (pos+1) dims fullSol acc
	            fun findInSubtree j acc'' =
	                if j = d then acc''
		        else findInSubtree (j+1)
		             (findAll' (concat [partSol, fromList[j]])
		                       (pos+1) dims acc'')
	        in
	            findInSubtree (i+1) acc'
                end
        in
    	    findAll' (fromList []) 0 alldims []
	end ;

end (* struct *) ;



(* Generic pruned search using a modulus functional *)

structure ModSearch : GENERIC_SEARCH = struct

(* Modulus operation for properties of 'points' (i.e. potential solutions) *)
(* Example of a sequentially realizable functional: uses local state *)
(* This is the only 'essential' use of an impure (imperative) feature in
   this approach, although we do allow ourselves the use of mutable arrays
   below for a bit more efficiency. *)

fun propertyWithModulus property point =
    let val inspected = Array.array (Array.length point, false)
        val log = ref ([]: (int*int) list)
    in (property (fn i =>
         (if Array.sub(inspected,i) then ()
          else (Array.update(inspected,i,true) ;
                log := (i,Array.sub(point,i))::(!log)) ;
          Array.sub(point,i))) ,
        !log)
        (* returns value of (property point), along with list of the distinct
           indices at which point was inspected, most recent first,
           and their values at these indices *)
    end ;

(* E.g.
   propertyWithModulus (fn g =>g(0)+g(2)+g(0)+g(1)=7) (tabulate(4,fn i=>i+1)) ;
 returns (true,[(1,2),(2,3),(0,1)])
*)

exception Finished ;

fun nextPoint' maxs ((i,j)::restOfLog) =
    if j < Array.sub(maxs,i) then (i,j+1)::restOfLog
    else nextPoint' maxs restOfLog
  | nextPoint' maxs [] = raise Finished ;

fun updateArrayWith arr [] = arr
  | updateArrayWith arr ((i,j)::rest) =
    (Array.update(arr,i,j) ; updateArrayWith arr rest) ;

fun nextPoint maxs log =
    updateArrayWith (Array.array(Array.length maxs,0)) (nextPoint' maxs log) ;
    (* Wasteful allocation here? Doesn't seem detrimental to performance. *)

fun nextPoint1 maxs log =
    SOME (nextPoint maxs log) handle Finished => NONE ;

fun arrayToList a = Array.foldr (fn (x,l) => x::l) [] a ;

fun findOne' property maxs coords =
    (case propertyWithModulus property coords of
       (true,_) => SOME (arrayToList coords)
     | (false,log) => findOne' property maxs (nextPoint maxs log)) ;

fun findAll' property maxs coords =
    (case propertyWithModulus property coords of
       (true,log)  => arrayToList (updateArrayWith
                           (Array.array(Array.length maxs,~1)) log) ::
                      (* ~1 used as wildcard *)
                      findAll'' property maxs (nextPoint1 maxs log)
     | (false,log) => findAll'' property maxs (nextPoint1 maxs log))
and findAll'' property maxs (SOME coords) = findAll' property maxs coords
  | findAll'' property maxs NONE = [] ;

exception EmptySpace ;

fun decrement n = if n>0 then n-1 else raise EmptySpace ;

fun startSearch searchOp default (prob:SearchProblem) =
    searchOp (#property prob)
             (Array.fromList (map decrement (#dimensions prob)))
             (Array.array ((List.length(#dimensions prob), 0)))
    handle EmptySpace => default | Finished => default ;

fun findOne (prob:SearchProblem) = startSearch findOne' NONE prob ;
fun findAll (prob:SearchProblem) = startSearch findAll' [] prob ;

end (* struct *) ;



(* Generic search using catchcont.
   This provides the effect of both pruning and backup. *)

structure CcSearch : GENERIC_SEARCH = struct

fun find register dims P =
    let val n = Array.length dims ;
        val path = Array.array (n, ~1) ;
        fun override p =
	    fn i => case Array.sub (path,i) of ~1 => p i | j => j ;
        fun search Q =
	    case Catchcont.catchcont0 (Q o override) of
	         inl answer => if #result answer then register path else ()
               | inr cont => case #arg cont of i => searchFrom (#resume cont) i 0
	and searchFrom R i j =
	    if j<Array.sub(dims,i) then (Array.update(path,i,j) ;
	                 search (R j) ;
			 searchFrom R i (j+1))
	    else Array.update(path,i,~1)
    in  search P
    end ;

fun arrayToList a = List.tabulate (Array.length a, fn i => Array.sub(a,i)) ;

fun findOne (prob:SearchProblem) =
    let exception Found of int array
    in  (find (fn path => raise Found path)
              (Array.fromList (#dimensions prob)) (#property prob) ; NONE)
        handle Found path => SOME (arrayToList path)
    end ;

fun findAll (prob:SearchProblem) =
    let val solutionList = ref ([] : int list list)
        fun push sol = (solutionList := (arrayToList sol) :: !solutionList)
    in  find push (Array.fromList (#dimensions prob)) (#property prob) ;
        List.rev (!solutionList)
    end ;

end (* struct *) ;
