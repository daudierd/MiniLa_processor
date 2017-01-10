-- ----------------------------------------------------------
--                                                         --
--       MiniLa language processor verified compiler       --
--                      SPECIFICATION                      --
--                                                         --
--                     DAUDIER, Dorian                     --
--            Special research student at JAIST            --
--                                                         --
-- ----------------------------------------------------------

in table.mod
in pnat.mod

mod! VAR principal-sort Var {
	[Var]
}

mod! EXP {
	pr(VAR)
	[Var ExpPNat < Exp]
	[Exp ErrExp < Exp&Err]
	op errExp : -> ErrExp {constr} .
	op 0 : -> ExpPNat {constr} .
	op s : ExpPNat -> ExpPNat {constr }
	op _+_ : Exp Exp -> Exp {constr l-assoc prec: 30} .
	op _+_ : Exp&Err Exp&Err -> Exp&Err .
	op sd : Exp Exp -> Exp {constr l-assoc prec: 30} .
	op sd : Exp&Err Exp&Err -> Exp&Err .
	op _*_ : Exp Exp -> Exp {constr l-assoc prec: 29} .
	op _*_ : Exp&Err Exp&Err -> Exp&Err .
	op _/_ : Exp Exp -> Exp {constr l-assoc prec: 29} .
	op _/_ : Exp&Err Exp&Err -> Exp&Err .
	op _%_ : Exp Exp -> Exp {constr l-assoc prec: 29} .
	op _%_ : Exp&Err Exp&Err -> Exp&Err .
}

mod! ENV { pr(PNAT) pr(VAR)
	pr(TABLE(
		K <= view from TRIV to VAR { sort Elt -> Var },
		V <= view from TRIV-ERR-IF to PNAT { sort Elt -> PNat, sort Err -> ErrPNat, sort Elt&Err -> PNat&Err, op err -> errPNat, op (if_then{_}else{_}) -> (if_then{_}else{_}) })
	* { sort Table -> Env, sort EmpTable -> EmpEnv, sort NeTable -> NeEnv, sort ErrTable -> ErrEnv, sort Table&Err -> Env&Err, op errTable -> errEnv, op empTable -> empEnv })
}

mod! STM { pr(EXP)
	[Stm]
	
	op estm : -> Stm {constr} .
	op _:=_; : Var Exp -> Stm {constr} .
	op _ _ : Stm Stm -> Stm {constr} .
}

mod! INTER { pr(PNAT) pr(EXP) pr(ENV) pr(STM)
	op inter : Stm -> Env&Err .
	op eval : Stm Env&Err -> Env&Err .
	op evalExp : ExpPNat Env -> PNat .
	op evalExp : Exp&Err Env&Err -> PNat&Err .
	
	-- equations
	var N : PNat . var EN : ExpPNat . vars E E1 E2 : Exp .
	var V : Var . var EV : Env . vars S S1 S2 : Stm . var EE : Env&Err .
	eq inter(S) = eval(S, empEnv) .
	
	eq eval(S, errEnv) = errEnv .
	eq eval(estm, EV) = EV .
	eq eval((V := E ;), EV) = update(EV,V,evalExp(E,EV)) .
	eq eval(S1 S2, EV) = eval(S2, eval(S1, EV)) .
	
	eq evalExp(E, errEnv) = errPNat .
	eq evalExp(0, EV) = 0 .
	eq evalExp(V, EV) = lookup(EV,V) .
	eq evalExp(s(EN),EV) = s(evalExp(EN,EV)) .
	eq evalExp(E1 + E2,EV) = evalExp(E1,EV) + evalExp(E2,EV) .
	eq evalExp(sd(E1,E2),EV) = sd(evalExp(E1,EV),evalExp(E2,EV)) .
	eq evalExp(E1 * E2,EV) = evalExp(E1,EV) * evalExp(E2,EV) .
	eq evalExp(E1 / E2,EV) = evalExp(E1,EV) quo evalExp(E2,EV) .
	eq evalExp(E1 % E2,EV) = evalExp(E1,EV) rem evalExp(E2,EV) .
}

mod! INSTR principal-sort Instr {
	pr(PNAT) pr(VAR)
	[Instr ErrInstr < Instr&Err]
	op errInstr : -> ErrInstr {constr} .
	op push : PNat -> Instr {constr} .
	op load : Var -> Instr {constr} .
	op store : Var -> Instr {constr} .
	op add : -> Instr {constr} .
	op minus : -> Instr {constr} .
	op mult : -> Instr {constr} .
	op div : -> Instr {constr} .
	op mod : -> Instr {constr} .
	op quit : -> Instr {constr} .
}

mod! LIST (E :: TRIV-ERR) principal-sort List { pr(PNAT)
	[List ErrList < List&Err]
	[Nil NnList < List]
	op nil : -> Nil {constr} .
	op errList : -> ErrList {constr} .
	op _|_ : Elt.E List -> NnList {constr} .
	op _|_ : Elt&Err.E List&Err -> List&Err .
	
	op _@_ : List List -> List {assoc} .
	op _@_ : List&Err List&Err -> List&Err .
	
	var E : Elt.E .
	vars L1 L2 : List .
	-- _@_
	eq nil @ L2 = L2 .
	eq (E | L1) @ L2 = E | (L1 @ L2) .
}


mod! ILIST principal-sort IList {
	pr(LIST(E <= view from TRIV-ERR to INSTR {
		sort Elt -> Instr, sort Err -> ErrInstr, sort Elt&Err -> Instr&Err, op err -> errInstr
	}) * {
		sort List -> IList, sort Nil -> Iln, sort NnList -> NnIList, sort ErrList -> ErrIList, sort List&Err -> IList&Err, op nil -> iln, op errList -> errIList })
}

mod! STACK {
	pr(LIST(E <= view from TRIV-ERR to PNAT {sort Elt -> PNat, sort Err -> ErrPNat, sort Elt&Err -> PNat&Err, op err -> errPNat}) * {sort List -> Stack, sort ErrList -> ErrStack, sort List&Err -> Stack&Err, op nil -> empstk, op errList -> errStack})
}

mod! VM {
	pr(ILIST)
	pr(STACK)
	pr(ENV)
	op vm : IList -> Env&Err .
	op exec : IList Stack&Err Env&Err -> Env&Err .
	
	-- equations
	var IL : IList . var PC : PNat . var SE : Stack&Err .
	var N : PNat . vars NE NE1 NE2 : PNat&Err .
	var V : Var . var EV : Env . var EE : Env&Err .
	
	eq vm(IL) = exec(IL, empstk, empEnv) .
	eq exec(IL, SE, errEnv) = errEnv .
	eq exec(IL, errStack, EV) = errEnv .
	eq exec(iln, SE, EV) = errEnv .
	
	eq exec(push(N) | IL, SE, EV) = exec(IL,N | SE, EV) .
	eq exec(load(V) | IL, SE, EV) = exec(IL, lookup(EV,V) | SE, EV) .
	eq exec(store(V) | IL, empstk, EV) = errEnv .
	eq exec(store(V) | IL, NE | SE, EV) = exec(IL, SE, update(EV,V,NE)) .
	
	eq exec(add | IL, empstk, EV) = errEnv .
	eq exec(add | IL, NE | empstk, EV) = errEnv .
	eq exec(add | IL, NE2 | NE1 | SE, EV) = exec(IL, NE1 + NE2 | SE, EV) .
	
	eq exec(minus | IL, empstk, EV) = errEnv .
	eq exec(minus | IL, NE | empstk, EV) = errEnv .
	eq exec(minus | IL, NE2 | NE1 | SE, EV) = exec(IL, sd(NE1,NE2) | SE, EV) .
	
	eq exec(mult | IL, empstk, EV) = errEnv .
	eq exec(mult | IL, NE1 | empstk, EV) = errEnv .
	eq exec(mult | IL, NE2 | NE1 | SE, EV) = exec(IL, NE1 * NE2 | SE, EV) .
	
	eq exec(div | IL, empstk, EV) = errEnv .
	eq exec(div | IL, NE | empstk, EV) = errEnv .
	eq exec(div | IL, NE2 | NE1 | SE, EV) = exec(IL, NE1 quo NE2 | SE, EV) .
	
	eq exec(mod | IL, empstk, EV) = errEnv .
	eq exec(mod | IL, NE | empstk, EV) = errEnv .
	eq exec(mod | IL, NE2 | NE1 | SE, EV) = exec(IL, NE1 rem NE2 | SE, EV) .
	
	eq exec(quit | IL, SE, EE) = EE .
}

mod! COMP { pr(EXP) pr(ILIST) pr(STM)
	op comp : Stm -> IList .
	op gen : Stm -> IList .
	op genExp : Exp -> IList .
	op en2n : ExpPNat -> PNat .
	
	-- equations
	var EN : ExpPNat . vars E E1 E2 : Exp .
	var V : Var . vars S S1 S2 : Stm .
	eq comp(S) = gen(S) @ (quit | iln) .
	
	eq gen(estm) = iln .
	eq gen(V := E ;) = genExp(E) @ (store(V) | iln) .
	eq gen(S1 S2) = gen(S1) @ gen(S2) .
	
	eq genExp(EN) = push(en2n(EN)) | iln .
	eq genExp(V) = load(V) | iln .
	eq genExp(E1 + E2) = genExp(E1) @ genExp(E2) @ (add | iln) .
	eq genExp(sd(E1,E2)) = genExp(E1) @ genExp(E2) @ (minus | iln) .
	eq genExp(E1 * E2) = genExp(E1) @ genExp(E2) @ (mult | iln) .
	eq genExp(E1 / E2) = genExp(E1) @ genExp(E2) @ (div | iln) .
	eq genExp(E1 % E2) = genExp(E1) @ genExp(E2) @ (mod | iln) .
	eq en2n(0) = 0 .
	eq en2n(s(EN)) = s(en2n(EN)) .
}

mod! VERIFY-COMP {
	pr(COMP)
	pr(INTER)
	pr(VM)
	
	op th : Stm -> Bool .
	op th1 : Var Exp -> Bool .
	op lemPev : ExpPNat Env&Err -> Bool .
	op lem1E : Exp IList Stack Env -> Bool .
	op lem1E : Exp IList Stack&Err Env&Err -> Bool .
	op lem1S : Stm IList Stack&Err Env&Err -> Bool .
	
	var E : Exp . var EN : ExpPNat . var V : Var . var S : Stm .
	var IL : IList . var SE : Stack&Err . var EV : Env . var EE : Env&Err .
	
	eq th(S) = (inter(S) = vm(comp(S))) .
	eq th1(V, E) = (inter(V := E ;) = vm(comp(V := E ;))) .
	eq lemPev(EN, EV) = (evalExp(EN, EV) = en2n(EN)) .
	eq lem1E(E, IL, SE, EE) = (exec(genExp(E) @ IL, SE, EE) = exec(IL, evalExp(E, EE) | SE, EE)) .
	eq lem1S(S, IL, SE, EE) = (exec(gen(S) @ IL, SE, EE) = exec(IL, SE, eval(S, EE))) .
}
