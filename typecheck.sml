(*** TYPE DECLARATIONS ***)

(* type datatype *)
datatype ty = const of string
            | var of string
            | constr of int * int
            | arrow of ty * ty
            | app of ty * ty list
type subst = (string * ty) list
exception Clash
exception OccChk

(* pre-abstract syntax datatype *)
datatype builtin = ADD | SUBTRACT | MULTIPLY | AND | OR
datatype preexpr = ival of int 
                 | bval of bool 
                 | opexpi of builtin * preexpr * preexpr
                 | opexpb of builtin * preexpr * preexpr
                 | eqexp of preexpr * preexpr 
                 | name of string 
                 | ifexp of preexpr * preexpr * preexpr 
                 | func of (preexpr list * preexpr) list
                 | apply of preexpr * preexpr list
                 | econst of int * int
                 | ecase of preexpr * alt list
and alt = ALT of int * (preexpr list) * preexpr



(*** HELPER FUNCTIONS ***)

(* contradicts: string * ty * subst -> boolean *)
fun contradicts n ty nil = false
  | contradicts n ty ((n',ty')::tl) = 
        if (n = n')
        then if (ty = ty') then false else true
        else (contradicts n ty tl)

(* occurscheck: string * ty -> bool *)
fun occurscheck n (const a) = false
  | occurscheck n1 (var n2) = if n1 = n2 then true else false
  | occurscheck n (arrow(ty1, ty2)) = 
        (occurscheck n ty1) orelse (occurscheck n ty2)

(* applysubst': string * subst -> ty *)   
fun applysubst' n (nil : subst) = (var n)
  | applysubst' n ((n',t')::tl) = 
        if (n = n')
        then t'
        else (applysubst' n tl)

(* applysubst: ty * subst -> ty *) 
fun applysubst (var n) slist = (applysubst' n slist)
  | applysubst (const a) slist = (const a)
  | applysubst (arrow(ty1, ty2)) slist = 
        arrow((applysubst ty1 slist), (applysubst ty2 slist))
     
(* containsubst: string * subst -> bool *)   
fun containsubst n nil = false
  | containsubst n ((n',_)::tl) = 
        if (n = n')
        then true
        else (containsubst n tl)

(* compose: subst * subst -> subst 
   compose': subst * subts * subst -> subst *)
fun compose subst1 subst2 = 
        let fun compose' nil nil subst3 = subst3
              | compose' nil ((n,ty)::tl) subst3 = 
                    if (containsubst n subst3)
                    then (compose' nil tl subst3)
                    else (compose' nil tl ((n,ty)::subst3))      
              | compose' ((n,ty)::tl) subst2  subst3 = 
                    let val ty' = (applysubst ty subst2)
                    in if ty' = var n 
                       then (compose' tl subst2 subst3) 
                       else (compose' tl subst2 ((n,ty')::subst3))
                    end
        in (compose' subst1 subst2 nil)
        end



(*** INSTANCE OF ***)
(* function to check if one type is an instance of another *)

fun instanceof t (var s) = true 
  | instanceof (arrow(t1, t2)) (arrow(t1', t2')) = 
        (instanceof t1 t1') andalso (instanceof t2 t2')
  | instanceof (app(t, nil)) (app(t', nil)) = instanceof t t'
  | instanceof (app(t, h::tl)) (app(t', h'::tl')) =
        (instanceof h h') andalso (instanceof (app(t, tl)) (app(t', tl')))
  | instanceof t1 t2 = if (t1 = t2) then true else false
        


(*** EQUAL TYPE ***)
(* function to check if one type is identical to another, but differently 
   named, its results is true/false and a list of name replacements *)

fun equaltype t1 t2 = 
        let fun equaltype' (var s1) (var s2) rlist = 
                    if ((contradicts s1 (var s2) rlist) 
                            orelse (contradicts s2 (var s1) rlist))
                    then raise Clash
                    else if (containsubst s1 rlist)
                         then if (containsubst s2 rlist)
                              then rlist
                              else ((s2, (var s1))::rlist)
                         else if (containsubst s2 rlist)
                              then ((s1, (var s2))::rlist)
                              else ((s1, (var s2))::(s2, (var s1))::rlist)
              | equaltype' (arrow(t1, t2)) (arrow(t1', t2')) rlist = 
                    (equaltype' t1 t1' (equaltype' t2 t2' rlist))
              | equaltype' (app(t, nil)) (app(t', nil)) rlist = 
                   (equaltype' t t' rlist)
              | equaltype' (app(t, h::tl)) (app(t', h'::tl')) rlist =
                   (equaltype' h h'(equaltype' (app(t,tl)) (app(t',tl')) rlist))
              | equaltype' t1 t2 rlist = 
                    if t1 = t2 then rlist else raise Clash
        in (true, (equaltype' t1 t2 nil)) handle Clash => (false, nil)
        end



(*** UNIFY ***)
(* function to check if two types can be reduced to a common type, 
   the result is true/false and the necessary substitutions *)
   
(* unify: (ty * ty) list -> bool * subst
   unify': (ty * ty) list * subst -> subst
   unifypair: (ty * ty) -> subst *)        
   
fun unifypair (var n) ty = if ty = (var n) 
                           then [] 
                           else if (occurscheck n ty) 
                                then raise OccChk 
                                else [(n, ty)]
  | unifypair ty (var n) = if ty = (var n) 
                           then [] 
                           else if (occurscheck n ty) 
                                then raise OccChk 
                                else [(n, ty)]
  | unifypair (const n1) (const n2) = if n1 = n2 then [] else raise Clash
  | unifypair (const n) _ = raise Clash
  | unifypair (arrow(ty1, ty3)) (arrow(ty2, ty4)) = 
        let val subst = (unifypair ty1 ty2)
            val ty3' = (applysubst ty3 subst)
            val ty4' = (applysubst ty4 subst)
            val subst' = (unifypair ty3' ty4')
        in (compose subst subst')
        end
  | unifypair (arrow(ty1, ty3)) _ = raise Clash

fun unify' nil subst = subst
  | unify' ((ty1,ty2)::tl) subst =
        let val ty1' = (applysubst ty1 subst)
            val ty2' = (applysubst ty2 subst)
            val subst' = (unifypair ty1' ty2') @ subst
        in (unify' tl subst')
        end
    
fun unify tylist = 
        (true, (unify' tylist [])) handle Clash => (false, [])
                                   handle OccChk => (false, [])
        


(*** EXPRESSION CHECKER ***)
(* a function to check the type of a provided pre-expression *)

(* the rest of this is commented out until I get around to fixing it...

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
  | tycheckexp (name n) g s slist ty = 
        let val preexp' = (lookup n g) handle Impossible => (lookup n s)
        in (tycheckexp preexp' g s slist ty)
        end
  | tycheckexp (ifexp (c, e1, e2)) g s slist ty =
        let val s1 = tycheckexp c g s slist (const "bool")
            val s2 = tycheckexp e1 g s s1 ty
            val s3 = tycheckexp e2 g s s2 ty
        in s3
        end



(*** CLAUSE CHECKER ***)
(* a function to check the type of one clause of a function definition *)

(* Description: tycheckclause : arglist * body * ctx * sign * subst * ty -> subst
   Step 1: match arglist types with argtys (argtys -> restype)
           add stuff to ctx (ctx=gamma, sign=sigma)
           modify subst as needed
   Step 2: type check body using mod ctx, sign, mod subst, restype *)

fun tycheckclause nil body ctx sign slist ty =
        (tycheckexp body ctx sign slist ty)
  | tycheckclause (arg::tl) body ctx sign slist ty =
        (* once again, a more general variable than 'x' must be used *)
        let val slist' = (tycheckexp arg ctx sign slist (var "x"))
        in (tycheckclause tl body ctx sign slist' ty)
        end



(*** DEFINITION CHECKER ***)
(* a function to check the type of each clause to check the type of a function *)



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

unify [(var "y", arrow(const "int",const "int")), 
       (var "x", const "bool"), 
       (var "z", arrow(var "x", var "y"))];
       
unify [(var "x", const "int"), 
       (var "y", arrow(var "x", const "string")), 
       (arrow(const "bool", const "int"), var "x")]


(* for tycheckexp *)

(* test case A-- should all return substitution lists *)
tycheckexp (ival 1) [] [] [] (var "a")
tycheckexp (bval true) [] [] [] (const "bool")
tycheckexp (opexpi (MULTIPLY, ival 2, ival 3)) [] [] [("a", const "int")] (var "a")
tycheckexp (opexpb (OR, bval true, bval false)) [] [] [("a", const "int")] (var "b")
tycheckexp (eqexp (bval true, bval false)) [] [] [] (const "bool")
tycheckexp (name "n") [("n", ival 1)] [] [] (var "x")
tycheckexp (ifexp (bval true, ival 1, ival 2)) [] [] [] (var "a")

(* test case B-- should all raise Contradiction exceptions *)
tycheckexp (ival 1) [] [] [("a", const "bool")] (var "a")
tycheckexp (bval true) [] [] [] (const "int")
tycheckexp (opexpi (MULTIPLY, ival 2, bval true)) [] [] [("a", const "int")] (var "a")
tycheckexp (opexpb (OR, bval true, bval false)) [] [] [("a", const "int")] (var "a")
tycheckexp (eqexp (ival 1, bval false)) [] [] [] (const "bool")
tycheckexp (ifexp (bval true, ival 1, bval true)) [] [] [] (var "b")
tycheckexp (name "n") [("n", ival 1)] [] [] (const "bool")

*)