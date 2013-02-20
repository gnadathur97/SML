
(**** DATATYPE DECLARATIONS ****)

datatype expr = ival of int 
		   | bval of bool 
		   | ADD of expr * expr 
		   | SUBTRACT of expr * expr 
		   | MULTIPLY of expr * expr 
		   | AND of expr * expr 
		   | OR of expr * expr 
		   | eqexp of expr * expr 
		   | name of string 
		   | ifexp of expr * expr * expr 
		   | func of expr list * expr 
		   | apply of expr * expr list 
		   | letexp of (expr * expr) list * expr 
		   | null
		   | cons of expr * expr
		   | closexp of clos
and env = ENV of (expr * clos) list
and clos = CLOS of expr * env;




(**** SAMPLE FUNCTIONS ****)

(* Note that these functions were written under the assumption that "head", "remaining", and "isempty" are separately written functions. *)

(* factorial *)
val fact = func ([name "x"], ifexp (eqexp (name "x", ival 0), ival 1, MULTIPLY (name "x", apply (name "fact", [SUBTRACT (name "x", ival 1)] ))));

(* map *)
val map = func([name "f", name "l"], ifexp (apply (name "isempty", [name "l"]), name "l", cons (apply (name "f", [apply (name "head", [name "l"])]), apply (name "map", [name "f", apply (name "remaining", [name "l"])]))));

(* append *)
val append = func([name "l1", name "l2"], ifexp (apply (name "isempty", [name "l1"]), name "l2", cons (apply (name "head", [name "l1"]), apply (name "append", [apply (name "remaining", [name "l1"]), name "l2"]))));

(* reverse *)
val reverse = func([name "l"], ifexp (apply (name "isempty", [name "l"]), name "l", apply (name "append", [apply (name "reverse", [apply (name "remaining", [name "l"] ) ] ), apply (name "head", [name "l"])])));




(**** ENVIRONMENT HELPER FUNCTIONS ****)

fun update(n, c, ENV nil) = ENV [(n, c)] | update(n, c, ENV l) = ENV((n, c)::l); 
fun lookup(n, ENV((n1, c1)::t)) = if (n = n1) then c1 else lookup(n, ENV t);

(* Do I need to raise an error in lookup if the name does not exist in the environment? *)




val testenv = ENV [(name "a", CLOS (ival 6, ENV [])), (name "b", CLOS (ival 7, ENV []))];

(**** INTERP FUNCTION ****)

fun interp (ival i, e) = CLOS(ival  i, e) 
     | interp (bval b, e) = CLOS(bval b, e) 
     | interp (ADD (exp1, exp2), env) = 
		let val CLOS(ival v1, _) = interp (exp1, env) 
		     val CLOS(ival v2, _) = interp (exp2, env) 
		in CLOS(ival (v1 + v2), env)
		end 
     | interp (SUBTRACT (exp1, exp2), env) = 
		let val CLOS(ival v1, _) = interp (exp1, env) 
		     val CLOS(ival v2, _) = interp (exp2, env)
		in CLOS(ival (v1 - v2), env)
		end
     | interp (MULTIPLY (exp1, exp2), env) = 
		let val CLOS(ival v1, _) = interp (exp1, env) 
		     val CLOS(ival v2, _) = interp (exp2, env)
		in CLOS(ival (v1 * v2), env)
		end 
     | interp (AND (exp1, exp2), env) = 
		let val CLOS (bval v1, _) = interp (exp1, env) 
		     val CLOS (bval v2, _) = interp (exp2, env) 
		in CLOS(bval (v1 andalso v2), env)
		end 
     | interp (OR (exp1, exp2), env) = 
		let val CLOS (bval v1, _) = interp (exp1, env) 
		     val CLOS (bval v2, _) = interp (exp2, env) 
		in CLOS(bval (v1 orelse v2), env)
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
		     fun combine (nil, _) = nil | combine (_, nil) = nil | combine (n::t1, c::t2) = (n, c)::combine(t1, t2)
		     val env'' = combine(fal, aal)
		in interp (body, ENV(env' @ env''))
		end    
     | interp (letexp (l, e), env) =
		let fun update' (nil, env') = env'
		          | update' ((n1, exp1)::t, env') = update' (t, update(n1, interp(exp1, env), env') )
		     val env' = update'(l, env)
		in interp(e, env')
		end  
     | interp (null, env) = CLOS(null, env)
     | interp (cons (e1, e2), env) =
		let val clos1 = interp(e1, env)
		     val clos2 = interp(e2, env)
		in CLOS(cons (closexp clos1, closexp clos2), env)
		end
     | interp (closexp C, env) = C;
