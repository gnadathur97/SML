(*** TYPE DECLARATIONS ***)

(* type datatype *)
datatype ty = const of string
            | var of string
            | constr of int * int
            | arrow of ty * ty
            | app of ty * ty list
type subst = (string * ty) list
exception Contradiction
exception Impossible

(* pre-abstract syntax datatype *)
datatype builtin = ADD | SUBTRACT | MULTIPLY | AND | OR
datatype preexpr = ival of int 
                 | bval of bool 
                 | opexpi of builtin * preexpr * preexpr
                 | opexpb of builtin * preexpr * preexpr
                 | eqexp of preexpr * preexpr 
                 | name of string 
                 | ifexp of preexpr * preexpr * preexpr 
              (* temporarily ignoring the following:
                 | func of preexpr list * preexpr 
                 | apply of preexpr * preexpr list
                 | econst of int * int
                 | ecase of preexpr * alt list *)



(*** HELPER FUNCTIONS ***)

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
        
(* applies a substitution to a variable *)
fun applysubst (var n) (nil : subst) = (var n)
  | applysubst (var n) ((n',t')::tl) = 
        if (n = n')
        then t'
        else (applysubst (var n) tl)
 | applysubst _ _ = raise Impossible
 
(* will instantiate one type with another *)
fun instant (var n) (var n') = (var n')



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
        


(*** EXPRESSION CHECKER ***)
(* a function to check the type of a provided pre-expression *)

(* Description: tycheckexp : preexp * tyenv * tyenv * subst * ty -> subst
   preexp-- the expression we want to check
   tyenv-- gamma, the local type environment
   tyenv-- sigma, the global type environment
   subst-- the current substitution list
   ty-- the expected type of preexp, what we want to check against
   subt-- tycheckexp returns a substitution *)
(* Note that ultimately there will be another function that will just return 
   true and a substitution list or false and an empty list *)

fun tycheckexp (ival i) g s slist (var n) = 
        if (contradicts n (const "int") slist)
        then raise Contradiction
        else if (contains n (const "int") slist)
             then slist
             else (n, (const "int"))::slist
  | tycheckexp (ival i) g s slist (const n) =
        if (n = "int") 
        then slist
        else raise Contradiction
  | tycheckexp (bval b) g s slist (var n) =
        if (contradicts n (const "bool") slist)
        then raise Contradiction
        else if (contains n (const "bool") slist)
             then slist
             else (n, (const "bool"))::slist
  | tycheckexp (bval b) g s slist (const n) =
        if (n = "bool") 
        then slist
        else raise Contradiction
  | tycheckexp (opexpi (_, v1, v2)) g s slist (var n) =
        if (contradicts n (const "int") slist)
        then raise Contradiction
        else let val s1 = tycheckexp v1 g s slist (const "int")
                 val s2 = tycheckexp v2 g s s1 (const "int")
             in if (contains n (const "int") s2)
                then s2
                else (n, (const "int"))::s2
             end
  | tycheckexp (opexpi (_, v1, v2)) g s slist (const n) =
        if (n = "int")
        then let val s1 = tycheckexp v1 g s slist (const "int")
                 val s2 = tycheckexp v2 g s s1 (const "int")
             in s2
             end
        else raise Contradiction
  | tycheckexp (opexpb (_, v1, v2)) g s slist (var n) =
        if (contradicts n (const "bool") slist)
        then raise Contradiction
        else let val s1 = tycheckexp v1 g s slist (const "bool")
                 val s2 = tycheckexp v2 g s s1 (const "bool")
             in if (contains n (const "bool") s2)
                then s2
                else (n, (const "bool"))::s2
             end
  | tycheckexp (opexpb (_, v1, v2)) g s slist (const n) =
        if (n = "bool")
        then let val s1 = tycheckexp v1 g s slist (const "bool")
                 val s2 = tycheckexp v2 g s s1 (const "bool")
             in s2
             end
        else raise Contradiction        
  | tycheckexp (eqexp (v1, v2)) g s slist (var n) =
        if (contradicts n (const "bool") slist)
        then raise Contradiction
        else let (* note: the type of v1 must be more generic than 'var x' *)
                 val s1 = tycheckexp v1 g s slist (var "x")
                 val s2 = tycheckexp v2 g s s1 (var "x")
             in if (contains n (const "bool") s2)
                then s2
                else (n, (const "bool"))::s2
             end
  | tycheckexp (eqexp (v1, v2)) g s slist (const n) =
        if (n = "bool")
        then let val s1 = tycheckexp v1 g s slist (var "x")
                 val s2 = tycheckexp v2 g s s1 (var "x")
             in s2
             end
        else raise Contradiction 
  (* note: the actual type of the name must be looked up from some 
     sort of type environment... *)
  | tycheckexp (name s') g s slist (var n) = 
        if (contradicts n (var "y") slist)
        then raise Contradiction
        else if (contains n (var "y") slist)
             then slist
             else (n, (var "y"))::slist
  | tycheckexp (ifexp (c, e1, e2)) g s slist ty =
        let val s1 = tycheckexp c g s slist (const "bool")
            val s2 = tycheckexp e1 g s s1 ty
            val s3 = tycheckexp e2 g s s2 ty
        in s3
        end



(*** TEST CASES ***)


(* for instanceof, equaltype, and unify *)                  

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


(* for tycheckexp *)

(* test case A-- should all return substitution lists *)
tycheckexp (ival 1) [] [] [] (var "a")
tycheckexp (bval true) [] [] [] (const "bool")
tycheckexp (opexpi (MULTIPLY, ival 2, ival 3)) [] [] [("a", const "int")] (var "a")
tycheckexp (opexpb (OR, bval true, bval false)) [] [] [("a", const "int")] (var "b")
tycheckexp (eqexp (bval true, bval false)) [] [] [] (const "bool")
tycheckexp (name "name") [] [] [] (var "a")
tycheckexp (ifexp (bval true, ival 1, ival 2)) [] [] [] (var "a")

(* test case B-- should all raise Contradiction exceptions *)
tycheckexp (ival 1) [] [] [("a", const "bool")] (var "a")
tycheckexp (bval true) [] [] [] (const "int")
tycheckexp (opexpi (MULTIPLY, ival 2, bval true)) [] [] [("a", const "int")] (var "a")
tycheckexp (opexpb (OR, bval true, bval false)) [] [] [("a", const "int")] (var "a")
tycheckexp (eqexp (ival 1, bval false)) [] [] [] (const "bool")
tycheckexp (ifexp (bval true, ival 1, bval true)) [] [] [] (var "b")