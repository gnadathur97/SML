
(**** DATATYPE DECLARATIONS ****)

datatype 'a option = NONE | SOME of 'a;

exception Impossible; (* for when invalid arguments get past type checking *)

datatype builtin = ADD | SUBTRACT | MULTIPLY | AND | OR;
            
datatype expr = ival of int 
              | bval of bool 
              | opexpi of builtin * expr * expr
              | opexpb of builtin * expr * expr
              | eqexp of expr * expr 
              | name of string 
              | ifexp of expr * expr * expr 
              | func of expr list * expr 
              | apply of expr * expr list 
              | letexp of (expr * expr) list * expr 
              | null
              | cons of expr * expr
              | closexp of clos
              | letrec of (expr * expr) list * expr
and env = ENV of (expr * clos option ref) list
and clos = CLOS of expr * env;



(**** SAMPLE FUNCTIONS ****)

(* Note that these functions were written under the assumption that "head", 
  "remaining", and "isempty" are separately written functions. *)

(* factorial *)
val fact = func ([name "x"], 
                 ifexp (eqexp (name "x", ival 0), 
                        ival 1, 
                        opexpi (MULTIPLY,
                                name "x", 
                                apply (name "fact", 
                                      [opexpi (SUBTRACT, name "x", ival 1)]))));
(* map *)
val map = func([name "f", name "l"], 
               ifexp (apply (name "isempty", [name "l"]), 
                      name "l", 
                      cons (apply (name "f", 
                                   [apply (name "head", [name "l"])]), 
                            apply (name "map", 
                                   [name "f", apply (name "remaining", [name "l"])]))));
(* append *)
val append = func([name "l1", name "l2"], 
                  ifexp (apply (name "isempty", [name "l1"]), 
                         name "l2", 
                         cons (apply (name "head", [name "l1"]), 
                               apply (name "append", 
                                      [apply (name "remaining", 
                                              [name "l1"]), name "l2"]))));
(* reverse *)
val reverse = func([name "l"], 
                   ifexp (apply (name "isempty", [name "l"]), 
                          name "l", 
                          apply (name "append", 
                                 [apply (name "reverse", 
                                         [apply (name "remaining", 
                                                 [name "l"])]), 
                                  apply (name "head", [name "l"])])));



(**** HELPER FUNCTIONS ****)

fun update(n, c, ENV nil) = ENV [(n, ref (SOME c))] 
  | update(n, c, ENV l) = ENV((n, ref (SOME c))::l); 
  
fun updatenull(n, ENV nil) = ENV [(n, ref NONE)] 
  | updatenull(n, ENV l) = ENV((n, ref NONE)::l);
  
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
		    val v2 = interp (exp2, env)
		    val v3 = interp (exp3, env)
		in if v1 then v2 else v3
		end
  | interp (func (args, exp), env) = CLOS (func (args, exp), env)
  | interp (apply (f, l), env) = 
	    let val CLOS(func (fal, body), ENV env') = interp (f, env)
		    val aal = map (fn x=> interp(x, env)) l
		    val env'' = combine(fal, aal)
		in interp (body, ENV(env' @ env''))
		end    
  | interp (letexp (l, e), env) =
		let fun update' (nil, env') = env'
		      | update' ((n1, exp1)::t, env') = 
		            update' (t, update(n1, interp(exp1, env), env'))
		     val env' = update'(l, env)
		in interp(e, env')
		end  
  | interp (null, env) = CLOS(null, env)
  | interp (cons (e1, e2), env) =
		let val clos1 = interp(e1, env)
		    val clos2 = interp(e2, env)
		in CLOS(cons (closexp clos1, closexp clos2), env)
		end
  | interp (closexp C, env) = C  
  | interp (letrec (l, e), env) =
       let fun updatenull'(nil, env) = env 
             | updatenull'((n1, e1)::t, env) = updatenull'(t, updatenull(n1, env))
           val env' = updatenull'(l, env)
           fun replace'(nil, env', returnval) = ()
             | replace'((n1, e1)::t, env', returnval) = 
                   replace'(t, env', replace(n1, SOME (interp (e1, env')), env'))
           val temp = replace'(l, env', ())
       in interp (e, env')
       end;



(*** MISCELLANEOUS ***)

(* Still need to add in a 'special' function to handle predefined 
   functions like 'head' and 'remaining' *)