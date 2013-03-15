(* note that it is easier to read output if the print depth is increased,
   try: Control.Print.printDepth := 100; *)

(**** DATATYPE DECLARATIONS ****)

datatype 'a option = NONE | SOME of 'a;

exception Impossible; (* for when invalid arguments get past type checking *)

datatype builtin = ADD | SUBTRACT | MULTIPLY | AND | OR;
            
datatype expr = ival of int 
              | bval of bool 
              | opexpi of builtin * expr * expr
              | opexpb of builtin * expr * expr
              | null
              | cons of expr * expr
              | head of expr
              | remaining of expr
              | isempty of expr
              | eqexp of expr * expr 
              | name of string 
              | ifexp of expr * expr * expr 
              | func of expr list * expr 
              | apply of expr * expr list 
              | letexp of (expr * expr) list * expr   
              | closexp of clos
              | letrec of (expr * expr) list * expr
and env = ENV of (expr * clos option ref) list
and clos = CLOS of expr * env;



(**** SAMPLE FUNCTIONS ****)

(* factorial *)
val myfact = func ([name "x"], 
                   ifexp (eqexp (name "x", ival 0), 
                          ival 1, 
                          opexpi (MULTIPLY,
                                  name "x", 
                                  apply (name "f", 
                                        [opexpi (SUBTRACT, name "x", ival 1)]))));
(* Test case: 
   val recurslet = letrec([(name "f", myfact)], apply(name "f", [ival 5]));
   val CLOS(x, _) = interp(recurslet, ENV []); *)

(* map *)                                  
val mymap = func([name "f", name "l"], 
                 ifexp (isempty (name "l"), 
                        name "l", 
                        cons (apply (name "f", 
                                     [head (name "l")]), 
                              apply (name "m", 
                                     [name "f", remaining (name "l")]))));
(* Test case:
   val square = func ([name "x"], opexpi(MULTIPLY, name "x", name "x"));
   val testlist = cons(ival 1, cons(ival 2, cons(ival 3, null)));                       
   val recurslet = letrec([(name "m", mymap), (name "f", square)], 
                       apply (name "m", [name "f", testlist]));                       
   val CLOS(x, _) = interp(recurslet, ENV []); *)  
                                   
(* append *)
val myappend = func([name "l1", name "l2"], 
                    ifexp (isempty (name "l1"), 
                           name "l2", 
                           cons (head (name "l1"), 
                                 apply (name "a", 
                                        [remaining (name "l1"), name "l2"]))));
(* Test case:
   val testlist1 = cons(ival 1, cons(ival 2, cons(ival 3, null)));
   val testlist2 = cons(ival 4, cons(ival 5, null));
   val recurslet = letrec([(name "a", myappend)], 
                          apply (name "a", [testlist1, testlist2]));                     
   val CLOS(x, _) = interp(recurslet, ENV []); *) 
   
(* reverse *)
val myreverse = func([name "l"], 
                     ifexp (isempty (name "l"), 
                            name "l", 
                            apply (name "a", 
                                   [apply (name "r", 
                                           [remaining (name "l")]),
                                   head (name "l")])));
(* Test case:
   val testlist = cons(ival 1, cons(ival 2, cons(ival 3, null)));
   val recurslet = letrec([(name "r", myreverse), (name "a", myappend)], 
                          apply (name "r", [testlist1]));                     
   val CLOS(x, _) = interp(recurslet, ENV []); *) 


(**** HELPER FUNCTIONS ****)

fun update(n, c, ENV nil) = ENV [(n, ref (SOME c))] 
  | update(n, c, ENV l) = ENV((n, ref (SOME c))::l); 
  
fun updatenull(n, ENV l) = ENV((n, ref NONE)::l);
  
fun replace(n, newclos, ENV nil) = raise Impossible
  | replace(n, newclos, ENV((n1, cref)::t)) = 
        if (n = n1) then cref := newclos else replace(n, newclos, ENV t);

fun lookup(n, ENV(nil)) = raise Impossible
  | lookup(n, ENV((n1, ref (SOME c1))::t)) = 
        if (n = n1) then c1 else lookup(n, ENV t);
  
fun combine(h::t, nil) = raise Impossible
  | combine(nil, h::t) = raise Impossible
  | combine(nil, nil) = nil
  | combine(n::t1, c::t2) = (n, ref (SOME c))::combine(t1, t2);
  
fun speciali(ADD, i1, i2) = i1 + i2
  | speciali(SUBTRACT, i1, i2) = i1 - i2
  | speciali(MULTIPLY, i1, i2) = i1 * i2;
  
fun specialb(AND, b1, b2) = b1 andalso b2
  | specialb(OR, b1, b2) = b1 orelse b2;
  


(**** INTERP FUNCTION ****)

fun interp (ival i, e) = CLOS(ival  i, e) 
  | interp (bval b, e) = CLOS(bval b, e) 
  | interp (opexpi (operator, exp1, exp2), env) = 
        let val CLOS(ival v1, _) = interp (exp1, env) 
            val CLOS(ival v2, _) = interp (exp2, env) 
        in CLOS(ival (speciali (operator, v1, v2)), env)
        end
  | interp (opexpb (operator, exp1, exp2), env) = 
        let val CLOS (bval v1, _) = interp (exp1, env) 
		    val CLOS (bval v2, _) = interp (exp2, env) 
        in CLOS(bval (specialb (operator, v1, v2)), env)
        end
  | interp (null, env) = CLOS(null, env)
  | interp (cons (e1, e2), env) =
        let val CLOS(v1, _) = interp(e1, env)
		    val CLOS(v2, _) = interp(e2, env)
        in CLOS(cons (v1, v2), env)
        end      
  | interp (head l, env) =
        let val CLOS (cons(h, _), _) = interp (l, env)
        in CLOS (h, env)
        end
  | interp (remaining l, env) =
        let val CLOS (cons(_, t), _) = interp (l, env)
        in CLOS (t, env)
        end
  | interp (isempty l, env) = 
        let val CLOS (v, _) = interp (l, env)
        in if v = null 
           then CLOS (bval true, env)
           else CLOS (bval false, env)
        end
  | interp (eqexp (exp1, exp2), env) = 
        let val CLOS (ival v1, _) = interp (exp1, env) 
		    val CLOS (ival v2, _) = interp (exp2, env) 
        in CLOS(bval (v1 = v2), env)
        end
  | interp (name n, env) = 
        let val CLOS(exp, _) = lookup(name n, env)
        in interp(exp, env)
        end
  | interp (ifexp (exp1, exp2, exp3), env) = 
        let val CLOS(bval v1, _) = interp (exp1, env)
        in if v1 then interp (exp2, env) else interp (exp3, env)
        end
  | interp (func (args, exp), env) = CLOS (func (args, exp), env)
  | interp (apply (f, l), env) = 
        let val CLOS(func (fal, body), ENV env') = interp (f, env)
		    val aal = map (fn x=> interp(x, env)) l
		    val env'' = combine(fal, aal)
        in interp (body, ENV(env'' @ env'))
        end    
  | interp (letexp (l, e), env) =
        let fun update' (nil, env') = env'
		      | update' ((n1, exp1)::t, env') = 
		            update' (t, update(n1, interp(exp1, env), env'))
		     val env' = update'(l, env)
        in interp(e, env')
        end  
  | interp (closexp C, env) = C  
  | interp (letrec (l, e), env) =
       let fun updatenull'(nil, env) = env
             | updatenull'((n1, e1)::t, env) = updatenull'(t, updatenull(n1, env))
           val env' = updatenull'(l, env)
           fun replace'(nil, env', returnval) = ()
             | replace'((n1, e1)::t, env', returnval) = 
                   replace'(t, env', replace(n1, SOME (interp (e1, env')), env'))
           val temp = replace'(rev l, env', ())
       in interp (e, env')
       end;
    
       

(* MISCELLANEOUS *)
(* I decided to temporarily ignore that members of a list can be functions for 
   simplicity, but here is the original cons case in interp:

  | interp (cons (e1, e2), env) =
        let val clos1 = interp(e1, env)
		    val clos2 = interp(e2, env)
        in CLOS(cons (closexp clos1, closexp clos2), env)
        end
*)