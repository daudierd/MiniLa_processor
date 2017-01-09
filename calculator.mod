in table.mod
in pnat.mod

mod! VAR principal-sort Var {
	[Var]
}

mod! EXP {
	pr(VAR)
	[Var ExpPNat < Exp]
	op 0 : -> ExpPNat {constr} .
	op s : ExpPNat -> ExpPNat {constr }
	op _+_ : Exp Exp -> Exp {constr l-assoc prec: 30} .
	op _-_ : Exp Exp -> Exp {constr l-assoc prec: 30} .
	op _*_ : Exp Exp -> Exp {constr l-assoc prec: 29} .
	op _/_ : Exp Exp -> Exp {constr l-assoc prec: 29} .
	op _%_ : Exp Exp -> Exp {constr l-assoc prec: 29} .
}

mod! ENV { pr(PNAT) pr(VAR)
	pr(TABLE(
		K <= view from TRIV to VAR { sort Elt -> Var },
		V <= view from TRIV-ERR-IF to PNAT { sort Elt -> PNat, sort Err -> ErrPNat, sort Elt&Err -> PNat&Err, op err -> errPNat, op (if_then{_}else{_}) -> (if_then{_}else{_}) })
	* { sort Table -> Env, sort EmpTable -> EmpEnv, sort NeTable -> NeEnv, sort ErrTable -> ErrEnv, sort Table&Err -> Env&Err, op errTable -> errEnv, op empTable -> empEnv })
}

mod! INTER { pr(PNAT) pr(EXP) pr(ENV)
	op inter : ExpPNat Env -> PNat .
	op inter : Exp Env&Err -> PNat&Err .
	op inter : Exp ErrEnv -> ErrPNat .
	
	-- equations
	var N : PNat . var EN : ExpPNat . vars E E1 E2 : Exp .
	var V : Var . var EV : Env .
	eq inter(E, errEnv) = errPNat .
	eq inter(0, EV) = 0 .
	eq inter(V, EV) = lookup(EV,V) .
	eq inter(s(EN),EV) = s(inter(EN,EV)) .
	eq inter(E1 + E2,EV) = inter(E1,EV) + inter(E2,EV) .
	eq inter(E1 - E2,EV) = sd(inter(E1,EV),inter(E2,EV)) .
	eq inter(E1 * E2,EV) = inter(E1,EV) * inter(E2,EV) .
	eq inter(E1 / E2,EV) = inter(E1,EV) quo inter(E2,EV) .
	eq inter(E1 % E2,EV) = inter(E1,EV) rem inter(E2,EV) .
}

mod! INSTR principal-sort Instr {
	pr(PNAT) pr(VAR)
	[Instr ErrInstr < Instr&Err]
	op errInstr : -> ErrInstr {constr} .
	op push : PNat -> Instr {constr} .
	op load : Var -> Instr {constr} .
	op add : -> Instr {constr} .
	op minus : -> Instr {constr} .
	op mult : -> Instr {constr} .
	op div : -> Instr {constr} .
	op mod : -> Instr {constr} .
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
	op vm : IList Env&Err -> PNat&Err .
	op exec : IList Stack&Err Env&Err -> PNat&Err .
	
	-- equations
	var IL : IList . var PC : PNat . var Stk : Stack .
	var N : PNat . vars NE NE1 NE2 : PNat&Err .
	var V : Var . var EV : Env . var EE : Env&Err .
	eq vm(IL, EE) = exec(IL, empstk, EE) .
	
	eq exec(IL, Stk, errEnv) = errPNat .
	eq exec(iln, empstk, EV) = errPNat .
	eq exec(iln, NE | empstk, EV) = NE .
	eq exec(iln, NE | NE1 | Stk, EV) = errPNat .
	
	eq exec(push(N) | IL, Stk, EV) = exec(IL,N | Stk, EV) .
	eq exec(load(V) | IL, Stk, EV) = exec(IL, lookup(EV,V) | Stk, EV) .
	
	eq exec(add | IL, empstk, EV) = errPNat .
	eq exec(add | IL, NE | empstk, EV) = errPNat .
	eq exec(add | IL, NE2 | NE1 | Stk, EV) = exec(IL, NE1 + NE2 | Stk, EV) .
	
	eq exec(minus | IL, empstk, EV) = errPNat .
	eq exec(minus | IL, NE | empstk, EV) = errPNat .
	eq exec(minus | IL, NE2 | NE1 | Stk, EV) = exec(IL, sd(NE1,NE2) | Stk, EV) .
	
	eq exec(mult | IL, empstk, EV) = errPNat .
	eq exec(mult | IL, NE1 | empstk, EV) = errPNat .
	eq exec(mult | IL, NE2 | NE1 | Stk, EV) = exec(IL, NE1 * NE2 | Stk, EV) .
	
	eq exec(div | IL, empstk, EV) = errPNat .
	eq exec(div | IL, NE | empstk, EV) = errPNat .
	eq exec(div | IL, NE2 | NE1 | Stk, EV) = exec(IL, NE1 quo NE2 | Stk, EV) .
	
	eq exec(mod | IL, empstk, EV) = errPNat .
	eq exec(mod | IL, NE | empstk, EV) = errPNat .
	eq exec(mod | IL, NE2 | NE1 | Stk, EV) = exec(IL, NE1 rem NE2 | Stk, EV) .
}

mod! COMP { pr(EXP) pr(ILIST)
	op comp : Exp -> IList .
	op en2n : ExpPNat -> PNat .
	
	-- equations
	var EN : ExpPNat . vars E E1 E2 : Exp .
	var V : Var .
	
	eq comp(EN) = push(en2n(EN)) | iln .
	eq comp(V) = load(V) | iln .
	eq comp(E1 + E2) = comp(E1) @ comp(E2) @ (add | iln) .
	eq comp(E1 - E2) = comp(E1) @ comp(E2) @ (minus | iln) .
	eq comp(E1 * E2) = comp(E1) @ comp(E2) @ (mult | iln) .
	eq comp(E1 / E2) = comp(E1) @ comp(E2) @ (div | iln) .
	eq comp(E1 % E2) = comp(E1) @ comp(E2) @ (mod | iln) .
	eq en2n(0) = 0 .
	eq en2n(s(EN)) = s(en2n(EN)) .
}

mod! VERIFY-COMP {
	pr(COMP)
	pr(INTER)
	pr(VM)
	
	op th : Exp Env -> Bool .
	op lemPev : ExpPNat Env -> Bool .
	op lem1 : Exp IList Stack&Err Env&Err -> Bool .
	
	var E : Exp . var EN : ExpPNat . var V : Var .
	var IL : IList . var Stk : Stack&Err . var EV : Env .
	eq th(E, EV) = (inter(E, EV) = vm(comp(E), EV)) .
	eq lemPev(EN, EV) = (inter(EN, EV) = en2n(EN)) .
	eq lem1(E, IL, Stk, EV) = (exec(comp(E) @ IL, Stk, EV) = exec(IL, vm(comp(E), EV) | Stk, EV)) .
}