(* Efficiency comparisons for various exact real integration operators,
   including one using catchcont. *)

(* Daniel Hillerström, October 2018 (heavily based on John Longley's
   implementation in SML) *)

(* We use int streams with digits 1,0,~1 to represent reals in [-1,1].
   So (int stream -> int stream) represents math functions [-1,1] ->
   [-1,1].

   We give four integration functions of the form: ...Integrate01 :
   int -> (int stream -> int stream) -> dyadic which perform definite
   integration from 0 to 1 with any specified precision.  More
   precisely, if F : int stream -> int stream represents f : [-1,1] ->
   [-1,1], then ...Integrate01 k F returns some dyadic within 2^-k of
   the true value of the integral of f from 0 to 1.

   In fact, for any given k and F, all four of our integrators will
   return the *same* dyadic approximation - they are all accessing the
   same information about F - so that efficiency comparisons between
   them are indeed meaningful. *)

(* #use "topfind";;
 * #require "zarith";; *)


type big = Z.t
let toBig = Z.of_int
let toSmall = Z.to_int

let print_small n =
  Printf.printf "%d%!" n

(* Memoized powers of two *)
let maxTwoExponent = 80
let maxTwoExponent' = Z.of_int maxTwoExponent
let two = Z.of_int 2

let two_to_array : Z.t array
  = Array.make maxTwoExponent Z.zero

let rec fill_two_to_array : int -> Z.t -> unit
  = fun i two_to_i ->
  if Z.equal (Z.of_int i) maxTwoExponent' then ()
  else (Array.set two_to_array i two_to_i;
        fill_two_to_array (i+1) (Z.mul two_to_i two))

let _ = fill_two_to_array 0 Z.one

let two_to i = Array.get two_to_array i

(* Basic dyadic arithmetic *)
type dyadic = big * int (* (a, k) represents a*2^k *)
let dyZero : dyadic = (Z.zero, -1)
let dyOne : dyadic = (Z.one, 0)
let dyHalf : dyadic = (Z.one, -1)
let dyMinusHalf : dyadic = (Z.minus_one, -1)
let string_of_dyadic (a, k) = Printf.sprintf "(%s, %d)" (Z.to_string a) k

let dyEqual : dyadic -> dyadic -> bool
  = fun (a, k) (a', k') -> k = k && Z.equal a a'

let four : Z.t = Z.of_int 4

let rec simp : dyadic -> dyadic
  = fun (a, k) ->
  let res = Z.rem a four in
  if Z.equal res Z.zero
  then if Z.equal a Z.zero
       then dyZero
       else simp (Z.div a four, k + 2)
  else if Z.equal res two
  then (Z.div a two, k + 1)
  else (a, k)

let add : dyadic -> dyadic -> dyadic
  = fun (a, k) (a', k') ->
  if k >= k'
  then let r = two_to (k - k') in
       (Z.(add (mul r a) a'), k')
  else let r = two_to (k' - k) in
       (Z.(add a (mul r a')), k)

let neg : dyadic -> dyadic
  = fun (a, k) -> (Z.neg a, k)

let sub : dyadic -> dyadic -> dyadic
  = fun d d' -> add d (neg d')

let mult : dyadic -> dyadic -> dyadic
  = fun (a, k) (a', k') -> (Z.mul a a', k + k')

let leq : dyadic -> dyadic -> bool
  = fun (a, k) (a', k') ->
  if k >= k'
  then let r = two_to (k - k') in
       Z.(leq (mul r a) a')
  else let r = two_to (k' - k) in
       Z.(leq a (mul r a'))

let rescale : dyadic -> int -> dyadic
  = fun (a, k) k' -> (a, k + k')

let average : dyadic -> dyadic -> dyadic
  = fun d d' -> rescale (add d d') (-1)

let (left_average, right_average) : ((dyadic -> dyadic -> dyadic) * (dyadic -> dyadic -> dyadic))
  = let thrice : dyadic -> dyadic
      = fun (a, k) -> (Z.(add a (add a a)), k)
    in
    (fun d d' -> rescale (add (thrice d) d') (-2)), (* (3d + d') / 4 *)
    (fun d d' -> rescale (add d (thrice d')) (-2))  (* (d + 3d') / 4 *)

let print_dyadic : dyadic -> unit
  = fun (a, k) ->
  Printf.printf "(%s, %d)%!" (Z.to_string a) k

(* Signed binary streams, representing reals in [~1,1]. Digits are 1,0,~1. *)
type 'a stream = Cons of 'a * (unit -> 'a stream)

let tail : 'a stream -> 'a stream = function
  | Cons (_, f) -> f ()

let rec const_stream : 'a -> 'a stream
  = fun x -> Cons (x, fun () -> const_stream x)

let rec append : 'a list -> 'a stream -> 'a stream
  = fun xs s ->
  match xs with
  | [] -> s
  | x :: xs -> Cons (x, fun () -> append xs s)


(* Produces stream rep of integer m in [-2^j,2^j), relative to
   [-2^j,2^j].  Will consist of just ~1 and 1, ending in an infinite
   tail of ~1s.  First j+1 digits will be the binary rep of m+2^j,
   writing ~1 for 0. *)
let rec stream_of_big : big -> int -> big stream
  = fun m j ->
  if j = 0
  then if Z.equal m Z.minus_one then const_stream Z.minus_one
       else Cons (Z.one, fun () -> const_stream Z.minus_one)
  else let j' = j - 1 in
       if Z.lt m Z.zero then Cons (Z.minus_one, fun () -> stream_of_big Z.(add m (two_to j')) j')
       else Cons (Z.one, fun () -> stream_of_big Z.(sub m (two_to j')) j')

(* Produces signed binary stream for dyadic in range [~1,1),
   consisting of just ~1 and 1 and ending in tail of ~1.  This choice
   of representation facilitates comparison with the catchcont
   implementation of integration. *)
let stream_of_dyadic : dyadic -> big stream
  = fun (a, k) -> stream_of_big a (-k)

(* returns centre of interval represented by a finite digit list *)
let rec dyadic_of_list : int -> big list -> dyadic
  = fun i xs ->
  match xs with
  | [] -> dyZero
  | x :: xs -> add (x, i) (dyadic_of_list (i - 1) xs)

let rec take : int -> 'a stream -> 'a list
  = fun i (Cons (x, f)) ->
  if i = 0 then []
  else if i = 1 then [x]
  else x :: take (i - 1) (f())

(* returns a dyadic within 2^-k of the true value of stream *)
let dyadic_of_stream : int -> big stream -> dyadic
  = fun k stream ->
  dyadic_of_list (-1) (take k stream)

let apply_to_precision : int -> ('a stream -> 'a stream) -> 'a stream -> dyadic
  = fun k f stream -> dyadic_of_stream k (f stream)

(* returns right end of interval represented by a finite digit list *)
let rec max_dyadic_of_list : int -> big list -> dyadic
  = fun k xs ->
  match xs with
  | [] -> (Z.one, k + 1)
  | x :: xs ->
     let d = max_dyadic_of_list (k - 1) xs in
     add (x, k) d

(* INTEGRATION OPERATIONS *)

(* Purely functional integration (Berger/Simpson) *)

(* We allow stream memoization to achieve the typical effect of
   a Haskell-style call-by-need implementation - we consider this
   to be within the spirit of 'pure functional' programming.
 *)

module Vector = struct
  type 'a t = 'a array

  let singleton : 'a -> 'a t
    = fun x -> Array.make 1 x

  let add : 'a t -> 'a -> 'a t
    = fun xs x -> Array.concat [xs; Array.make 1 x]

  let length : 'a t -> int
    = Array.length

  let get : 'a t -> int -> 'a
    = Array.get
end

let rec memo_stream' : int -> ('a Vector.t * (unit -> 'a stream)) ref -> 'a stream
  = fun i memo ->
  match !memo with
  | (xs, f) when i < Vector.length xs ->
     Cons (Vector.get xs i, fun () -> memo_stream' (i + 1) memo)
  | (xs ,f) ->
     let (Cons (x, f')) = f () in
     memo := (Vector.add xs x, f');
     Cons (x, fun () -> memo_stream' (i + 1) memo)

let memo_stream : 'a stream -> 'a stream
  = fun (Cons (x, f)) ->
  let memo = ref (Vector.singleton x, f) in
  memo_stream' 0 memo

let rec critical_stream : (big stream -> dyadic) -> dyadic -> big list -> big stream
  = fun g y xs ->
  let stream =
    memo_stream (Cons (Z.minus_one, fun () -> critical_stream g y (xs @ [Z.minus_one])))
  in
  let r = g (append xs stream) in
  if not (dyEqual r y) then stream
  else Cons (Z.one, fun () -> critical_stream g y (xs @ [Z.one]))

let rec fun_integrate' : (big stream -> dyadic) -> big list -> dyadic option -> dyadic
  = fun g xs z ->
  let y = match z with
    | Some y' -> y'
    | None -> g (append xs (const_stream Z.minus_one))
  in
  let r = g (append xs (critical_stream g y xs)) in
  if dyEqual r y then rescale y (1 - List.length xs)
  else add
         (fun_integrate' g (xs @ [Z.minus_one]) z) (* passing [z] here saves recomputing G (ds @ -1,-1,-1,...) *)
         (fun_integrate' g (xs @ [Z.one]) None)

let fun_integrate01 : int -> (big stream -> big stream) -> dyadic
  = fun k f ->
  let fn = apply_to_precision k f in
  simp (fun_integrate' fn [Z.one] None)

(* Slower version omitting memoization, for comparison: *)
let rec slow_critical_stream : (big stream -> dyadic) -> dyadic -> big list -> big stream
  = fun g y xs ->
  let stream =
    Cons (Z.minus_one, fun () -> slow_critical_stream g y (xs @ [Z.minus_one]))
  in
  let r = g (append xs stream) in
  if not (dyEqual r y) then stream
  else Cons (Z.one, fun () -> slow_critical_stream g y (xs @ [Z.one]))

let rec slow_fun_integrate' : (big stream -> dyadic) -> big list -> dyadic option -> dyadic
  = fun g xs z ->
  let y = match z with
    | Some y' -> y'
    | None -> g (append xs (const_stream Z.minus_one))
  in
  let r =
    let stream' =
      slow_critical_stream g y xs
    in
    g (append xs stream')
  in
  if dyEqual r y then rescale y (1 - List.length xs)
  else add
         (slow_fun_integrate' g (xs @ [Z.minus_one]) z)
         (slow_fun_integrate' g (xs @ [Z.one]) None)

let slow_fun_integrate01 : int -> (big stream -> big stream) -> dyadic
  = fun k f ->
  let fn = apply_to_precision k f in
  simp (slow_fun_integrate' fn [Z.one] None)

(* Stream modulus functional, implemented using local state.
   Example of a sequentially realizable functional. *)
let result_with_modulus : (big stream -> 'a) -> big stream -> 'a * big list
  = fun f stream ->
  let log : big list ref = ref [] in
  let rec log_stream (Cons (x, g)) =
    (log := x :: !log;
     Cons (x, fun () -> log_stream ( g() ) ))
  in
  let result =
    let stream' = log_stream stream in
    f stream'
  in
  (result, List.rev !log)


(* Integration using modulus functional *)
let eq_one : dyadic -> bool
  = fun (a, k) -> (Z.equal a (two_to (-k)))

(* Integrates [f] from [start] up to 1, with precision [k] *)
let mod_integrate : int -> (big stream -> big stream) -> dyadic -> dyadic
  = fun k f start ->
  let rec sweep x total =
    if eq_one x then total
    else let (y, modulus) =
           let fn = apply_to_precision k f in
           result_with_modulus fn (stream_of_dyadic x)
         in
         let new_x = max_dyadic_of_list (-1) modulus in
         let res = sub new_x x in
         let res = mult y res in
         let res = add total res in
         sweep new_x res
  in
  sweep start dyZero

let mod_integrate01 : int -> (big stream -> big stream) -> dyadic
  = fun k f ->
  simp (mod_integrate k f dyZero)


(* Integration using effect handlers. *)
effect Branch : big stream

let branch : unit -> big stream
  = fun () -> perform Branch

let eff_integrate' : int -> (unit -> dyadic) -> dyadic
  = fun i g ->
  let integrate' g =
    match g () with
    | v ->
       (fun i -> rescale v i)
    | effect Branch k ->
       (fun i ->
         (* [Obj.clone] clones the continuation prior to invoking it,
            thereby simulating multi-shot continuations. *)
         let resume x = continue (Obj.clone k) x in
         let lhs =
           resume (Cons (Z.minus_one, more)) (i - 1)
         in
         let rhs =
           resume (Cons (Z.one, more)) (i - 1)
         in
         add lhs rhs)
  in
  integrate' g i

let eff_integrate01 : int -> (big stream -> big stream) -> dyadic
  = fun k f ->
  let comp () = apply_to_precision k f (Cons (Z.one, more)) in
  simp (eff_integrate' 0 comp)

(* Example: Squaring *)
exception SquareError

let rec square_stream' : int -> int -> dyadic -> dyadic -> (unit -> big stream) -> big stream
  = fun in_wt out_wt sq_min sq_max u ->
  if leq dyZero sq_min then
    Cons (Z.one, fun () ->
                 let sq_min' = sub (rescale sq_min 1) dyOne in
                 let sq_max' = sub (rescale sq_max 1) dyOne in
                 square_stream' in_wt (out_wt - 1) sq_min' sq_max' u)
  else if leq sq_max dyZero then
    Cons (Z.minus_one, fun () ->
                       let sq_min' = add (rescale sq_min 1) dyOne in
                       let sq_max' = add (rescale sq_max 1) dyOne in
                       square_stream' in_wt (out_wt - 1) sq_min' sq_max' u)
  else if leq dyMinusHalf sq_min && leq sq_max dyHalf then
    Cons (Z.zero, fun () ->
                  let sq_min' = rescale sq_min 1 in
                  let sq_max' = rescale sq_max 1 in
                  square_stream' in_wt (out_wt - 1) sq_min' sq_max' u)
  else match u () with
       | Cons (i, u') when Z.equal i Z.one ->
          let sq_min' =
            let s = (Z.one, 2 * in_wt - out_wt) in
            sub (average sq_min sq_max) s
          in
          square_stream' (in_wt - 1) out_wt sq_min' sq_max u'
       | Cons (i, u') when Z.equal i Z.minus_one ->
          let sq_max' =
            let s = (Z.one, 2 * in_wt - out_wt) in
            sub (average sq_min sq_max) s
          in
          square_stream' (in_wt - 1) out_wt sq_min sq_max' u'
       | Cons (i, u') when Z.equal i Z.zero ->
          let sq_min' =
            let s = (Z.of_int 3, 2 * in_wt - 2 - out_wt) in
            sub (left_average sq_min sq_max) s
          in
          let sq_max' =
            let s = (Z.of_int 3, 2 * in_wt - 2 - out_wt) in
            sub (right_average sq_min sq_max) s
          in
          square_stream' (in_wt - 1) out_wt sq_min' sq_max' u'
       | _ -> raise SquareError

let rec neg_stream : big stream -> big stream
  = fun (Cons (x, u)) -> Cons (Z.neg x, fun () -> neg_stream ( u() ))

let rec square : big stream -> big stream
  = fun (Cons (x, u)) ->
  if Z.equal x Z.one then
    square_stream' (-1) 0 dyZero dyOne u
  else if Z.equal x Z.minus_one then
    square_stream' (-1) 0 dyZero dyOne (fun () -> neg_stream ( u() ))
  else if Z.equal x Z.zero then
    Cons (Z.zero, fun () -> Cons (Z.zero, (fun () -> square ( u() ))))
  else
    raise SquareError

(* Logistic map: x -> 1 - 2x^2. Iterations of this behave chaotically. *)
let logistic : big stream -> big stream
  = fun stream ->
  let (Cons (_, u)) = square stream in
  neg_stream ( u() )

let rec iter : int -> ('a -> 'a) -> 'a -> 'a
  = fun n f x ->
  if n = 0 then x
  else let n' = n - 1 in
       let x' = f x in
       iter n' f x'

let id : 'a -> 'a
  = fun x -> x

(* For timing experiments: *)
let time2 f x y = (* TODO *)
  f x y

let integration_funs = [
    ("slow_fun", slow_fun_integrate01);
    ("fun", fun_integrate01);
    ("mod", mod_integrate01);
    ("eff", eff_integrate01)
  ];;

(* #use "bench.ml";; *)

open Bench

exception InvalidArgument

let validateId20 ((z,i) : dyadic) = Z.equal z Z.one && i = -1
let validateSquare14 ((z, i) : dyadic) = Z.(equal z (of_int 44739467)) && i = -27
let validateSquare17 ((z, i) : dyadic) = Z.(equal z (of_int 2863312299)) && i = -33
let validateSquare20 ((z, i) : dyadic) = Z.(equal z (of_int 183251940523)) && i = -39

let validateFun (fname, n) =
  match fname with
  | "id" when n = 20 ->validateId20
  | "square" -> (match n with
                   14 -> validateSquare14
                | 17  -> validateSquare17
                | 20  -> validateSquare20
                | _   -> raise InvalidArgument)
  | _ -> raise InvalidArgument

let funToIntegrate = function
  | "id" -> id
  | "square" -> square
  | _ -> raise InvalidArgument

let numIterations = 1
let integrationFuns : (string * int) -> (dyadic Bench.t list)
    = fun (f, n) -> [{ m = 0; n = n; niter = numIterations; label = "slowFun"; f = (let g = funToIntegrate f in (fun () -> slow_fun_integrate01 n g)); validate = validateFun (f, n) };
                    { m = 0; n = n; niter = numIterations; label = "fun"; f = (let g = funToIntegrate f in (fun () -> fun_integrate01 n g)); validate = validateFun (f, n) };
                    { m = 0; n = n; niter = numIterations; label = "mod"; f = (let g = funToIntegrate f in (fun () -> mod_integrate01 n g)); validate = validateFun (f, n) };
                    { m = 0; n = n; niter = numIterations; label = "eff"; f = (let g = funToIntegrate f in (fun () -> eff_integrate01 n g)); validate = validateFun (f, n) }]

let rec cartesian = function
  | ([],        _)  -> []
  | ((x :: xs), ys) -> List.map (fun y -> (x, y)) ys @ cartesian (xs, ys)

let typicalId = List.concat (List.map (fun (f, arg) -> f arg) (cartesian ([integrationFuns], [("id", 20)])))
let typicalSquare = List.concat (List.map (fun (f, arg) -> f arg) (cartesian ([integrationFuns], [("square", 14); ("square", 17); ("square", 20)])))

let validateLogisticFun (m, n) : (dyadic -> bool)
    = match m with
  | 15 -> (match n with
           | 1 -> (fun (z,i) -> Z.(equal z (of_int 357913429)) && i = -30)
           | 2 -> (fun (z,i) -> Z.(equal z (of_int (-6299289887))) && i = -35)
           | 3 -> (fun (z,i) -> Z.(equal z (of_int (-9360359951))) && i = -36)
           | 4 -> (fun (z,i) -> Z.(equal z (of_int (-42633981081))) && i = -40)
           | 5 -> (fun (z,i) -> Z.(equal z (of_int (-16548145409))) && i = -40)
           | _ -> raise InvalidArgument)
        | 10 -> (match n with
                 | 8 -> (fun (z,i) -> Z.(equal z (of_int (-13383190727))) && i = -41)
                 | _ -> raise InvalidArgument)
        |  5 -> (match n with
                 | 10 -> (fun (z,i) -> Z.(equal z (of_int (-6233913477))) && i = -38)
                 | _ -> raise InvalidArgument)
        | _ -> raise InvalidArgument


let logistic : (int * int) -> (dyadic Bench.t list)
    = fun (m, n) -> [ { m = m; n = n; niter = numIterations; label = "mod"; f = (fun () -> mod_integrate01 m (iter n logistic)); validate = validateLogisticFun (m, n) };
                      { m = m; n = n; niter = numIterations; label = "eff"; f = (fun () -> eff_integrate01 m (iter n logistic)); validate = validateLogisticFun (m, n) }
    ]

let logisticSuite = List.concat (List.map (fun (f, arg) -> f arg) (cartesian ([logistic], [(15, 1); (15, 2); (15, 3); (15, 4); (15, 5); (10, 8); (5, 10)])))

let main () =
  (* Bench.run_suite "integration-id-ocaml.csv" typicalId;
   * Bench.run_suite "integration-square-ocaml.csv" typicalSquare; *)
  Bench.run_suite "integration-logistic-ocaml.csv" logisticSuite

let _ = main()
