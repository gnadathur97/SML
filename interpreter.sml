(* note that it is easier to read output if the print depth is increased,
   try: Control.Print.printDepth := 100; *)

(**** DATATYPE DECLARATIONS ****)

datatype 'a option = NONE | SOME of 'a

exception Impossible; (* for when invalid arguments get past type checking *)

datatype builtin = ADD | SUBTRACT | MULTIPLY | AND | OR
            
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
              | letrec of (expr * expr) list * expr
              | econst of int * int
              | ecase of expr * alt list
              | clos of expr * env
and alt = ALT of int * (expr list) * expr
and env = ENV of (expr * expr option ref) list



(**** HELPER FUNCTIONS ****)

fun update(n, e, ENV l) = ENV((n, ref (SOME e))::l)
  
fun updatenull(n, ENV l) = ENV((n, ref NONE)::l)
  
fun replace(n, newexp, ENV nil) = raise Impossible
  | replace(n, newexp, ENV((n', eref)::t)) = 
        if (n = n') then eref := newexp else replace(n, newexp, ENV t)

fun lookup(n, ENV(nil)) = raise Impossible
  | lookup(n, ENV((n1, ref (SOME e1))::t)) = 
        if (n = n1) then e1 else lookup(n, ENV t)
  
fun combine(h::t, nil) = raise Impossible
  | combine(nil, h::t) = raise Impossible
  | combine(nil, nil) = nil
  | combine(n::t1, c::t2) = (n, ref (SOME c))::combine(t1, t2)
  
fun speciali(ADD, i1, i2) = i1 + i2
  | speciali(SUBTRACT, i1, i2) = i1 - i2
  | speciali(MULTIPLY, i1, i2) = i1 * i2
  
fun specialb(AND, b1, b2) = b1 andalso b2
  | specialb(OR, b1, b2) = b1 orelse b2
  


(**** INTERP FUNCTION ****)

fun interp (ival i, _) = ival  i
  | interp (bval b, _) = bval b
  | interp (opexpi (operator, exp1, exp2), env) = 
        let val ival v1 = interp (exp1, env) 
            val ival v2 = interp (exp2, env) 
        in ival (speciali (operator, v1, v2))
        end
  | interp (opexpb (operator, exp1, exp2), env) = 
        let val bval v1 = interp (exp1, env) 
		    val bval v2 = interp (exp2, env) 
        in bval (specialb (operator, v1, v2))
        end
  | interp (eqexp (exp1, exp2), env) = 
        let val ival v1 = interp (exp1, env) 
		    val ival v2 = interp (exp2, env) 
        in bval (v1 = v2)
        end
  | interp (name n, env) = 
        let val e = lookup(name n, env)
        in case e of clos(e', _) => interp(e', env)
                   | _ => e
        end
  | interp (ifexp (exp1, exp2, exp3), env) = 
        let val bval v1 = interp (exp1, env)
        in if v1 then interp (exp2, env) else interp (exp3, env)
        end
  | interp (func (args, exp), env) = clos (func (args, exp), env)
  | interp (apply (e, l), env) = 
		let val aal = map (fn x=> interp(x, env)) l
		    val e' = interp (e, env)
		in case e' of clos(func(fal, body), ENV env') =>
		                  let val env'' = combine(fal, aal)
		                  in interp (body, ENV(env'' @ env'))
		                  end
		            | econst(_, _) => apply(e', aal)
		            | _ => raise Impossible
        end      
  | interp (letexp (l, e), env) =
        let fun update' (nil, env') = env'
              | update' ((n1, exp1)::t, env') = 
                    update' (t, update(n1, interp(exp1, env), env'))
            val env' = update'(l, env)
        in interp(e, env')
        end   
  | interp (letrec (l, e), env) =
       let fun updatenull'(nil, env) = env
             | updatenull'((n1, e1)::t, env) = updatenull'(t, updatenull(n1, env))
           val env' = updatenull'(l, env)
           fun replace'(nil, env', _) = ()
             | replace'((n1, e1)::t, env', _) = 
                   replace'(t, env', replace(n1, SOME(interp(e1,env')), env'))
           val _ = replace'(rev l, env', ())
       in interp (e, env')
       end   
  | interp (econst (tag, arity), env) = econst(tag, arity)
  | interp (ecase (e, altl), env) =
        let val e' = interp (e, env)
            fun lookupalt(tag, expl, nil) = raise Impossible
              | lookupalt(tag, expl, (ALT(tag', argl, ex))::tl) =
                    if tag = tag' 
                    then let val ENV env' = env
                             val env'' = combine(argl, expl)
                         in interp(ex, ENV(env'' @ env'))
                         end
                    else lookupalt(tag, expl, tl)
        in case e' of econst(t, _) => lookupalt(t, [], altl)
                    | apply(econst(t, _), l) => lookupalt(t, l, altl)
                    | _ => raise Impossible
        end
  | interp (clos (e, env), _) = clos (e, env)



(**** SAMPLE FUNCTIONS ****)

(* factorial *)
val myfact = func ([name "x"], 
                   ifexp (eqexp (name "x", ival 0), 
                          ival 1, 
                          opexpi (MULTIPLY,
                                  name "x", 
                                  apply (name "f", 
                                        [opexpi (SUBTRACT, name "x", ival 1)]))))
(* factorial test case: 
   val testval = ival 5
   val recurslet = letrec([(name "f", myfact)], apply(name "f", [testval]))
   val x = interp(recurslet, ENV []) 
*)

(* list constructors and helper functions: *)
val null = econst(0, 0)
val cons = econst(1, 2)
val isempty = func ([name "l"],
                    (ecase (name "l", 
                            [ALT (0, [], bval true),
                             ALT (1, [name "h", name "t"], bval false)])))
val head = func ([name "l"],
                 (ecase (name "l",
                         [ALT (0, [], null),
                          ALT (1, [name "h", name "t"], name "h")])))
val remaining = func ([name "l"],
                 (ecase (name "l",
                         [ALT (0, [], null),
                          ALT (1, [name "h", name "t"], name "t")])))

(* map *)
val mymap = func([name "f", name "l"], 
                 ifexp (apply (isempty, [name "l"]), 
                        name "l", 
                        apply (cons,
                               [apply (name "f", [apply (head, [name "l"])]),
                                apply (name "m", 
                                       [name "f", 
                                        apply (remaining, [name "l"])])])))
val mymap = func([name "f", name "l"], 
                 ecase (name "l",
                        [ALT (0, [], name "l"),
                         ALT (1, 
                              [name "h", name "t"], 
                              apply (cons, 
                                     [apply (name "f", [name "h"]), 
                                      apply (name "m", [name "f", name "t"])]))]))
(* map test case:
   val square = func ([name "x"], opexpi(MULTIPLY, name "x", name "x"))
   val testlist = apply(cons, 
                        [ival 1, apply(cons, 
                                       [ival 2, apply(cons, 
                                                [ival 3, null])])])                       
   val recurslet = letrec([(name "m", mymap), (name "f", square)], 
                          apply (name "m", [name "f", testlist]))                       
   val x = interp(recurslet, ENV [])
*)

(* append *)
val myappend = func([name "l1", name "l2"],
                    ifexp (apply (isempty, [name "l1"]), 
                           name "l2", 
                           apply (cons,
                                 [apply (head, [name "l1"]),
                                  apply (name "a", 
                                         [apply (remaining, [name "l1"]), 
                                          name "l2"])])))
val myappend = func([name "l1", name "l2"], 
                    ecase (name "l1",
                           [ALT (0, [], name "l2"),
                            ALT (1, 
                                 [name "h", name "t"], 
                                 apply (cons, 
                                        [name "h", 
                                        apply (name "a", [name "t", name "l2"])]))]))
(* append test case:
   val testlist1 = apply(cons, 
                        [ival 1, apply(cons, 
                                       [ival 2, apply(cons, 
                                                [ival 3, null])])])
   val testlist2 = apply(cons, 
                        [ival 4, apply(cons, 
                                       [ival 5, null])])
   val recurslet = letrec([(name "a", myappend)], 
                          apply (name "a", [testlist1, testlist2]))                
   val x = interp(recurslet, ENV [])
*)

(* reverse *)
val myreverse = func([name "l"], 
                     ifexp (apply (isempty, [name "l"]), 
                            name "l", 
                            apply (name "a", 
                                   [apply (name "r", 
                                           [apply (remaining, [name "l"])]), 
                                    apply (cons, [apply (head, [name "l"]), 
                                           null])])))
val myreverse = func([name "l"], 
                     ecase (name "l",
                            [ALT (0, [], name "l"),
                             ALT (1, 
                                  [name "h", name "t"], 
                                  apply (name "a", 
                                         [apply (name "r", [name "t"]), 
                                          apply(cons, [name "h", null])]))]))
(* reverse test case:
   val testlist = apply(cons, 
                        [ival 1, apply(cons, 
                                       [ival 2, apply(cons, 
                                                [ival 3, null])])])
   val recurslet = letrec([(name "r", myreverse), (name "a", myappend)], 
                          apply (name "r", [testlist]))                     
   val x = interp(recurslet, ENV [])
*)


(*** todo: address all 'match-nonexhaustive' warnings 
     in the helper function section ***)