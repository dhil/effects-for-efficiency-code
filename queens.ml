(* Comparing solutions to the n queens problem via various
   generic search algorithms and via a bespoke implementation. *)

(* Daniel Hillerström, November 2018, heavily based on John Longleyøs
   implementation in SML. *)

(* #use "generic_search.ml";; *)
open Generic_search
(* All our generic search operations take an input of type SearchProblem.
   We here give two ways of presenting n queens as a SearchProblem,
   parametric in n. *)

(* First way: nQueens : int -> SearchProblem *)

(* This doesn't refrain from querying the proposed solution p
   repeatedly on the same argument i.
   E.g. (p 0) is evaluated afresh for each comparison with some (p i), i>0.
   All our generic search implementations are robust enough to cope with this. *)

let test_queen_pair : (int -> int) -> int -> int -> bool
  = fun p i j ->
  let (jpos, ipos) =
    (* The let-bindings may appear to be irrelevant, but they are
       absolutely crucial to ensure left-to-right evaluation order.
       Writing `(p j, p i)` is equivalent to `let ipos = p i in let
       jpos = p j in ...` in OCaml. The exact evaluation order is
       crucial to guarantee that the search procedures yield the
       results in the same order. *)
    let jpos = p j in
    let ipos = p i in
    jpos, ipos
  in
  not (ipos = jpos || ipos - jpos = i - j || ipos - jpos = j - i)

let rec test_queen_pairs_from : (int -> int) -> int -> int -> bool
  = fun p i j ->
  i = j || (test_queen_pair p i j && test_queen_pairs_from p i (j + 1))

let rec test_queens_from : int -> (int -> int) -> int -> bool
  = fun n p i ->
  i = n || (test_queen_pairs_from p i 0 && test_queens_from n p (i + 1))

let n_queens : int -> search_problem
  = fun n ->
  { dimensions = List.tabulate n (fun _ -> n);
    property = fun p -> test_queens_from n p 0 }

(* Second way: nQueens : int -> SearchProblem *)

(* This remembers results of earlier queries to p, and in fact asks for
   each of p 0, p 1, ... once only, in this order. *)
let rec test_against : int -> int -> int list -> bool
  = fun y j zs ->
  match zs with
  | [] -> true
  | z :: zs ->
     z <> y && abs (z - y) <> j && test_against y (j + 1) zs

let rec test_from : int -> (int -> int) -> int -> int list -> bool
  = fun n p i zs ->
  if i = n then true
  else let y = p i in
       test_against y 1 zs && test_from n p (i + 1) (y :: zs)

let n_queens' : int -> search_problem
  = fun n ->
  { dimensions = List.tabulate n (fun _ -> n);
    property = (fun p -> test_from n p 0 []) }

(* Efficiency comparisons between nQueens and nQueens' are interesting
   (see below for some typical tests).  In general, nQueens' is
   faster, though more dramatically so for some generic search
   algorithms than others.  In particular, pruned search (without
   backup) is much more competitive for nQueens' than for nQueens.
   Advantage of backup is more strikingly visible for nQueens. *)

(* BESPOKE implementation of n queens problem, for comparison *)

module Bespoke_Queens = struct
  let test_queen_pair : int array -> int -> int -> bool
    = fun a i j ->
    let (jpos, ipos) = a.(j), a.(i) in
    not (ipos = jpos || ipos - jpos = i - j || ipos - jpos = j - i)

  let rec test_queen_pairs_from : int array -> int -> int -> bool
    = fun a i j ->
    j = i || (test_queen_pair a i j && test_queen_pairs_from a i (j + 1))

  exception Found of int array

  let rec search_all_extensions : int -> int array -> int -> unit
    = fun n a i ->
    if i = n then raise (Found a)
    else search_all_extensions_from n a i 0
  and search_all_extensions_from : int -> int array -> int -> int -> unit
    = fun n a i j ->
    if j = n then ()
    else (a.(i) <- j;
          ignore(if test_queen_pairs_from a i 0
                 then search_all_extensions n a (i + 1) else ());
          search_all_extensions_from n a i (j + 1))

  let rec search_all_extensions' : int list list -> int -> int array -> int -> int list list
    = fun acc n a i ->
    if i = n then Array.to_list a :: acc
    else search_all_extensions_from' acc n a i 0
  and search_all_extensions_from' : int list list -> int -> int array -> int -> int -> int list list
    = fun acc n a i j ->
    if j = n then acc
    else (a.(i) <- j;
          let acc' =
            if test_queen_pairs_from a i 0
            then search_all_extensions' acc n a (i + 1)
            else acc
          in
          search_all_extensions_from' acc' n a i (j + 1))

  let find_one : int -> int list option
    = fun n ->
    try
      search_all_extensions n (Array.make n 0) 0;
      None
    with Found a -> Some (Array.to_list a)

  let find_all : int -> int list list
    = fun n -> List.rev (search_all_extensions' [] n (Array.make n 0) 0)
end


let time f x = (* TODO *) f x

let naive_one_q n = time Naive_Search.find_one (n_queens n)
let naive_one_q' n = time Naive_Search.find_one (n_queens' n)
let naive_all_q n = time Naive_Search.find_all (n_queens n)
let naive_all_q' n = time Naive_Search.find_all (n_queens' n)

let fun_one_q n = time Fun_Search.find_one (n_queens n)
let fun_one_q' n = time Fun_Search.find_one (n_queens' n)

let mod_one_q n = time Mod_Search.find_one (n_queens n)
let mod_one_q' n = time Mod_Search.find_one (n_queens' n)
let mod_all_q n = time Mod_Search.find_all (n_queens n)
let mod_all_q' n = time Mod_Search.find_all (n_queens' n)

let eff_one_q n = time Eff_Search.find_one (n_queens n)
let eff_one_q' n = time Eff_Search.find_one (n_queens' n)
let eff_all_q n = time Eff_Search.find_all (n_queens n)
let eff_all_q' n = time Eff_Search.find_all (n_queens' n)

let bespoke_one_q n = time Bespoke_Queens.find_one n
let bespoke_all_q n = time Bespoke_Queens.find_all n

(* Some typical results.

Note that the absolute time taken for a given search implementation to find the
first n queens solution will vary erratically with n, as it will depend on
where the first solution happens to lie within the search space.
For 'findOne' experiments, therefore, only the time ratios between different
implementations for the same n are meaningful.

(1) Using nQueens : searchProblem *)

let all_q = [("naive", naive_all_q);
             ("mod", mod_all_q);
             ("eff", eff_all_q);
             ("bespoke", bespoke_all_q)]

let one_q = [("naive", naive_one_q);
             ("fun", fun_one_q);
             ("mod", mod_one_q);
             ("eff", eff_one_q);
             ("bespoke", bespoke_one_q)]

(* (2) Using nQueens' : searchProblem *)
let all_q' = [("naive", naive_all_q');
             ("mod", mod_all_q');
             ("eff", eff_all_q');
             ("bespoke", bespoke_all_q)]

let one_q' = [("naive", naive_one_q');
             ("fun", fun_one_q');
             ("mod", mod_one_q');
             ("eff", eff_one_q');
             ("bespoke", bespoke_one_q)]

let validateAllQ12 xs = List.length xs = 14200
let validateAllQ10 xs = List.length xs = 724
let validateAllQ8 xs = List.length xs = 92
let validateOne12 x = x = Some [0;2;4;7;9;11;5;10;1;6;8;3]
let validateOne16 x = x = Some [0;2;4;1;12;8;13;11;14;5;15;6;3;10;7;9]
let validateOne20 x = x = Some [0;2;4;1;3;12;14;11;17;19;16;8;15;18;7;9;6;13;5;10]
let validateOne24 x = x = Some [0;2;4;1;3;8;10;13;17;21;18;22;19;23;9;20;5;7;11;15;12;6;16;14]
let validateOne28 x = x = Some [0;2;4;1;3;8;10;12;14;16;22;24;21;27;25;23;26;6;11;15;17;7;9;13;19;5;20;18]

exception InvalidArgument

let validateOne = function
  | 12 -> validateOne12
  | 16 -> validateOne16
  | 20 -> validateOne20
  | 24 -> validateOne24
  | 28 -> validateOne28
  | _ -> raise InvalidArgument

let validateAll = function
  | 8 -> validateAllQ8
  | 10 -> validateAllQ10
  | 12 -> validateAllQ12
  | _ -> raise InvalidArgument;;


(* #use "bench.ml";; *)
open Bench
let numIterations = 11
let oneQ n = [
    { m = 0; n = n; niter = numIterations; label = "fun"; f = if n < 28 then (fun () -> fun_one_q n) else (fun () -> None); validate = validateOne n };
    { m = 0; n = n; niter = numIterations; label = "mod"; f = (fun () -> mod_one_q n); validate = validateOne n };
    { m = 0; n = n; niter = numIterations; label = "cc"; f = (fun () -> eff_one_q n); validate = validateOne n };
    { m = 0; n = n; niter = numIterations; label = "bespoke"; f = (fun () -> bespoke_one_q n); validate = validateOne n }
  ]

let oneQ' n = [
    { m = 0; n = n; niter = numIterations; label = "funP"; f = if n < 28 then (fun () -> fun_one_q' n) else (fun () -> None); validate = validateOne n };
    { m = 0; n = n; niter = numIterations; label = "modP"; f = (fun () -> mod_one_q' n); validate = validateOne n };
    { m = 0; n = n; niter = numIterations; label = "ccP"; f = (fun () -> eff_one_q' n); validate = validateOne n }
  ]

let allQ n = [
    { m = 0; n = n; niter = numIterations; label = "naive"; f = if n > 8 then (fun () -> []) else (fun () -> naive_all_q n); validate = validateAll n };
    { m = 0; n = n; niter = numIterations; label = "mod"; f = (fun () -> mod_all_q n); validate = validateAll n };
    { m = 0; n = n; niter = numIterations; label = "cc"; f = (fun () -> eff_all_q n); validate = validateAll n };
    { m = 0; n = n; niter = numIterations; label = "bespoke"; f = (fun () -> bespoke_all_q n); validate = validateAll n }
]

let allQ' n = [
    { m = 0; n = n; niter = numIterations; label = "naiveP"; f = if n > 8 then (fun () -> []) else (fun () -> naive_all_q' n); validate = validateAll n };
    { m = 0; n = n; niter = numIterations; label = "modP"; f = (fun () -> mod_all_q' n); validate = validateAll n };
    { m = 0; n = n; niter = numIterations; label = "ccP"; f = (fun () -> eff_all_q' n); validate = validateAll n }
  ]

let rec cartesian = function
  | ([], _) -> []
  | ((x :: xs), ys) -> List.map (fun y -> (x, y)) ys @ cartesian (xs, ys)

let apply (f, x) = f x

let findOneSuite = List.concat (List.map apply (cartesian ([oneQ;oneQ'], [12; 16; 20; 24; 28])))
let findAllSuite = List.concat (List.map apply (cartesian ([allQ;allQ'], [8; 10; 12])))

let runSuites () =
    let _ = run_suite "queens-find-one-ocaml.csv" findOneSuite in
    run_suite "queens-find-all-ocaml.csv" findAllSuite

let _ = runSuites ()
