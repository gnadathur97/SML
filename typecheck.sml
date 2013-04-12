(* TYPE DECLARATIONS *)
datatype ty = const of string
            | var of string
            | constr of int * int
            | arrow of ty * ty
            | app of ty * ty list
type subst = (string * ty) list
exception Contradiction



(*** HELPER FUNCTIONS **)

(* checks if a substitution is currently in the substitutions list *)
fun contains (v1 : string) (v2 : ty) (nil : subst) = false
  | contains v1 v2 ((v1',v2')::t) = 
        if ((v1 = v1') andalso (v2 = v2'))
        then true
        else (contains v1 v2 t)
        
(* checks if a substitution contradicts the current substitutions *)
fun contradicts (v1 : string) (v2 : ty) (nil : subst) = false
  | contradicts v1 v2 ((v1',v2')::t) = 
        if (v1 = v1')
        then if (v2 = v2') then false else true
        else (contradicts v1 v2 t)



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
        let fun equaltype' (var s1) (var s2) rlist = 
                    if ((contradicts s1 (var s2) rlist) 
                            orelse (contradicts s2 (var s1) rlist))
                    then raise Contradiction
                    else if (contains s1 (var s2) rlist)
                         then if (contains s2 (var s1) rlist)
                              then rlist
                              else ((s2, (var s1))::rlist)
                         else if (contains s2 (var s1) rlist)
                              then ((s1, (var s2))::rlist)
                              else ((s1, (var s2))::(s2, (var s1))::rlist)
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



(*** UNIFY ***)
(* function to check if two types can be reduced to a common type, 
   the result is true/false and the necessary substitutions *)

fun unify nil = (false, nil)
  | unify typelist = 
        let fun unify' (var n1) (var n2) slist =
                    if ((contradicts n1 (var n2) slist) 
                            orelse (contradicts n2 (var n1) slist))
                    then raise Contradiction
                    else if (contains n1 (var n2) slist)
                         then if (contains n2 (var n1) slist)
                              then slist
                              else ((n2, (var n1))::slist)
                         else if (contains n2 (var n1) slist)
                              then ((n1, (var n2))::slist)
                              else ((n1, (var n2))::(n2, (var n1))::slist)
              | unify' t (var n) slist = 
                    if (contradicts n t slist) 
                    then raise Contradiction 
                    else if (contains n t slist)
                         then slist
                         else ((n, t)::slist)
              | unify' (var n) t slist = 
                    if (contradicts n t slist)
                    then raise Contradiction
                    else if (contains n t slist)
                         then slist
                         else ((n, t)::slist)
              | unify' (arrow(t1, t2)) (arrow(t1', t2')) slist = 
                    (unify' t1 t1' (unify' t2 t2' slist))
              | unify' (app(t, nil)) (app(t', nil)) slist = 
                    (unify' t t' slist)
              | unify' (app(t, h::tl)) (app(t', h'::tl')) slist =
                    (unify' h h'(unify' (app(t,tl)) (app(t',tl')) slist))
              | unify' t1 t2 slist =
                    if t1 = t2 then slist else raise Contradiction
            fun unify'' nil slist = slist
              | unify'' ((t1, t2)::tl) slist = (unify'' tl (unify' t1 t2 slist))
        in (true, (unify'' typelist nil)) handle Contradiction => (false, nil)
        end
        


(*** TEST CASES ***)                  
(* test case 1-- instanceof: true, equaltype: false, unify: true *)             
val t1 = arrow(const "int", arrow(arrow(const "int", const "int"), const "bool"))
val t2 = arrow(var "alpha", var "beta")

(* test case 2-- instanceof: true, equaltype: true, unify: true *)
val t3 = arrow(arrow(var "alpha", var "beta"), var "alpha")
val t4 = arrow(arrow(var "delta", var "gamma"), var "delta")

(* test case 3-- instanceof: false, equaltype: false, unify: true *)
val t5 = arrow(var "beta", const "bool")
val t6 = arrow(arrow(const "int", const "int"), var "alpha")

(* test case 4-- instanceof: false, equaltype: false, unify: false *)
val t7 = const "bool"
val t8 = arrow(var "alpha", const "int")

(* test case 5-- using constr and app *)
val t9 = app(constr(1,3), [const "int", const "bool", var "alpha"])
val t10 = app(constr(1,3), [var "x", var "y", var "z"])