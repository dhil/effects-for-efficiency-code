
(* Resumable exception operators: catchcont and catchcont0. *)
(* Implemented in New Jersey SML using explicit continuations. *)

(* John Longley, mostly October 2015 *)


datatype ('a,'b) Sum = inl of 'a | inr of 'b 

signature CATCHCONT = sig

val catchcont : ((''r->'s)->(''t0*'t1)) ->
    ( {result :''t0, more :(''r->'s)->'t1} ,
      {arg :''r, resume :'s->(''r->'s)->(''t0*'t1)} ) Sum

val catchcont0 : ((''r->'s)->''t) ->
    ( {result :''t} ,
      {arg :''r, resume :'s->(''r->'s)->''t} ) Sum

end ;

structure Catchcont : CATCHCONT = struct 

type ('r,'s,'t0,'t1) Catchcont =
     ( {result :'t0, more :('r->'s)->'t1} ,
       {arg :'r, resume :'s->('r->'s)->('t0*'t1)} ) Sum ;

local open SMLofNJ.Cont in
fun catchcont (F:(''r->'s)->(''t0*'t1)) = 
    let val gStore = ref (NONE : (''r -> 's) option) 
        val returnAddress = ref (NONE : (''t0 * 't1) cont option)
    in
        callcc (fn k =>
	let val answer as (ground, rest) =
	    F (fn i:''r => 
	        case !gStore of 
		    SOME g => g i
	          | NONE => callcc (fn l => 
			throw k (inr {
                            arg = i, 
			    resume = fn j => fn g => 
				callcc (fn m =>
				   (gStore := SOME g ;
				    returnAddress := SOME m ;
				    throw l j))
                            })))
	in case !returnAddress of
	    NONE => inl {
                result = ground, 
                more = fn g => (gStore := SOME g ; rest)
                }
	  | SOME m => throw m answer
	end)
    end
end ;

fun catchcont0 (F:(''r->'s)->''t) =
    case catchcont (fn g => (F g,())) of
       inl answer => inl {result = #result answer}
     | inr cont   => inr {arg = #arg cont,
                          resume = fn j => fn g => #1 (#resume cont j g)}
(* Implementing catchcont0 directly gives no significant performance gain *)

end (* struct *) ;
