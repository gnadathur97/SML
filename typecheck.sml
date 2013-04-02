(* TYPE DECLARATIONS *)
datatype ty = int
            | bool
            | var of string
            | constr of int * int
            | arrow of ty * ty
            | app of ty * ty list

exception Contradiction

(* Question: is it necessary to specify that app's first argument is a constr? *)



(*** INSTANCE OF ***)
(* function to check if one type is an instance of another *)

fun instanceof t (var s) = true 
  | instanceof (arrow(t1, t2)) (arrow(t1', t2')) = 
        (instanceof t1 t1') andalso (instanceof t2 t2')
  | instanceof (app(t, nil)) (app(t', nil)) = instanceof t t'
  | instanceof (app(t, h::tl)) (app(t', h'::tl')) =
        (instanceof h h') andalso (instanceof (app(t, tl)) (app(t', tl')))
  | instanceof t1 t2 = if t1 = t2 then true else false



(*** EQUAL TYPE ***)
(* function to check if one type is identical to another, but differently 
   named, its results is true/false and a list of name replacements *)

fun equaltype t1 t2 = 
        let (* check if a replacement is in list *)
            fun containsr v1 v2 nil = false
              | containsr v1 v2 ((v1',v2')::t) = 
                    if ((v1 = v1') andalso (v2 = v2'))
                    then true
                    else (containsr v1 v2 t)
            (* check if a replacement contradicts the current replacements *)
            fun contradictsr v1 v2 nil = false
              | contradictsr v1 v2 ((v1',v2')::t) = 
                    if (v1 = v1')
                    then if (v2 = v2') then false else true
                    else (contradictsr v1 v2 t)
            fun equaltype' (var s1) (var s2) rlist = 
                    if (contradictsr s1 s2 rlist) 
                    then raise Contradiction
                    else if (containsr s1 s2 rlist) 
                         then rlist
                         else (s1,s2)::rlist
              | equaltype' (arrow(t1, t2)) (arrow(t1', t2')) rlist = 
                    (equaltype' t1 t1' (equaltype' t2 t2' rlist))
              | equaltype' (app(t, nil)) (app(t', nil)) rlist = 
                   (equaltype' t t' rlist)
              | equaltype' (app(t, h::tl)) (app(t', h'::tl')) rlist =
                   (equaltype' h h'(equaltype' (app(t,tl)) (app(t',tl')) rlist))
              | equaltype' t1 t2 rlist = 
                    if t1 = t2 then rlist else raise Contradiction
        in (true, (equaltype' t1 t2 nil)) handle Contradiction => (false, nil)
        end



(*** UNITY ***)
(* function to check if two types can be reduced to a common type, 
   the result is true/false and the necessary substitutions *)

fun unity t1 t2 = 
        let fun contradicts v1 v2 nil = false
              | contradicts v1 v2 ((v1',v2')::t) = 
                    if (v1 = v1')
                    then if (v2 = v2') then false else true
                    else (contradicts v1 v2 t)
            fun unity' t (var n) slist = 
                    if (contradicts n t slist) 
                    then raise Contradiction 
                    else (n, t)::slist
              | unity' (var n) t slist = 
                    if (contradicts n t slist)
                    then raise Contradiction
                    else (n, t)::slist
              | unity' (arrow(t1, t2)) (arrow(t1', t2')) slist = 
                    (unity' t1 t1' (unity' t2 t2' slist))
              | unity' (app(t, nil)) (app(t', nil)) slist = 
                    (unity' t t' slist)
              | unity' (app(t, h::tl)) (app(t', h'::tl')) slist =
                    (unity' h h'(unity' (app(t,tl)) (app(t',tl')) slist))
              | unity' t1 t2 slist =
                    if t1 = t2 then slist else raise Contradiction
        in (true, (unity' t1 t2 nil)) handle Contradiction => (false, nil)
        end



(*** TEST CASES ***)                  
(* test case 1-- instanceof: true, equaltype: false, unity: true *)             
val t1 = arrow(int, arrow(arrow(int, int), bool))
val t2 = arrow(var "alpha", var "beta")

(* test case 2-- instanceof: true, equaltype: true, unity: true *)
val t3 = arrow(arrow(var "alpha", var "beta"), var "alpha")
val t4 = arrow(arrow(var "delta", var "gamma"), var "delta")

(* test case 3-- instanceof: false, equaltype: false, unity: true *)
val t5 = arrow(var "beta", bool)
val t6 = arrow(arrow(int, int), var "alpha")

(* test case 4-- instanceof: false, equaltype: false, unity: false *)
val t7 = bool
val t8 = arrow(var "alpha", int)

(* test case 5-- using constr and app *)
val t9 = app(constr(1,3), [int, bool, var "alpha"])
val t10 = app(constr(1,3), [var "x", var "y", var "z"])