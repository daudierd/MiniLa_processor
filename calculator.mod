in table.mod

mod! PNAT principal-sort PNat {
	[PZero NzPNat < PNat]
	[PNat ErrPNat < PNat&Err]
	op 0 : -> PZero {constr} .
	op s : PNat -> NzPNat {constr} .
	op errPNat : -> ErrPNat {constr} .
	op if_then{_}else{_} : Bool PNat&Err PNat&Err -> PNat&Err .
	op _<_ : PNat PNat -> Bool .
	op _<_ : PNat&Err PNat&Err -> Bool .
	op _+_ : PNat PNat -> PNat {assoc comm} .
	op _+_ : PNat&Err PNat&Err -> PNat&Err .
	op _*_ : PNat PNat -> PNat {assoc comm} .
	op _*_ : PNat&Err PNat&Err -> PNat&Err .
	op sd : PNat PNat -> PNat .
	op sd : PNat&Err PNat&Err -> PNat&Err .
	op _quo_ : PNat NzPNat -> PNat .
	op _quo_ : PNat PZero -> ErrPNat .
	op _quo_ : PNat&Err PNat&Err -> PNat&Err .
	op _rem_ : PNat NzPNat -> PNat .
	op _rem_ : PNat PZero -> ErrPNat .
	op _rem_ : PNat&Err PNat&Err -> PNat&Err .
	
	-- equations
	vars M N : PNat . var NzN : NzPNat .
	vars ME NE : PNat&Err .
	
		-- properties of Peano numbers
		eq (s(N) = 0) = false .
		eq (s(N) = s(M)) = (N = M) .
		eq (errPNat = N) = false .
		
		-- Comparison and conditional statement
		eq if true then {NE} else {ME} = NE .
		eq if false then {NE} else {ME} = ME .
		eq (0 < NzN) = true .
		eq (N < 0) = false .
		eq (s(M) < s(N)) = (M < N) .
		
		eq (errPNat < N) = false .
		eq (NE < errPNat) = false .
		
		-- arithmetic operations
		eq 0 + N = N .
		eq s(N) + M = s(N + M) .
		eq NE + errPNat = errPNat .
		eq errPNat + NE = errPNat .
		
		eq 0 * N = 0 .
		eq s(N) * M = (N * M) + M .
		eq NE * errPNat = errPNat .
		eq errPNat * NE = errPNat .
		
		eq sd(0,N) = N .
		eq sd(s(N),0) = s(N) .
		eq sd(s(N),s(M)) = sd(N,M) .
		eq sd(NE,errPNat) = errPNat .
		eq sd(errPNat,NE) = errPNat .
		
		eq 0 quo NzN = 0 .
		eq M quo NzN = if (M < NzN) then { 0 } else { s((sd(M,NzN) quo NzN)) } .
		eq M quo 0 = errPNat .
		eq NE quo errPNat = errPNat .
		eq errPNat quo NE = errPNat .
		
		eq 0 rem NzN = 0 .	
		eq M rem NzN = if (M < NzN) then { M } else { (sd(M,NzN) rem NzN) } .
		eq M rem 0 = errPNat .
		eq NE rem errPNat = errPNat .
		eq errPNat rem NE = errPNat .
}

mod! VAR principal-sort Var {
	[Var]
}

mod! EXP {
	pr(VAR)
	[Var ExpPNat < Exp]
	[Exp ErrExp < Exp&Err]
	op errExp : -> ErrExp {constr} .
	op 0 : -> ExpPNat {constr} .
	op s : ExpPNat -> ExpPNat {constr} .
	op _+_ : Exp Exp -> Exp {constr l-assoc prec: 30} .
	op _+_ : Exp&Err Exp&Err -> Exp&Err .
	op _-_ : Exp Exp -> Exp {constr l-assoc prec: 30} .
	op _-_ : Exp&Err Exp&Err -> Exp&Err .
	op _*_ : Exp Exp -> Exp {constr l-assoc prec: 29} .
	op _*_ : Exp&Err Exp&Err -> Exp&Err .
	op _/_ : Exp Exp -> Exp {constr l-assoc prec: 29} .
	op _/_ : Exp&Err Exp&Err -> Exp&Err .
	op _%_ : Exp Exp -> Exp {constr l-assoc prec: 29} .
	op _%_ : Exp&Err Exp&Err -> Exp&Err .
	op _===_ : Exp Exp -> Exp {constr prec: 40 l-assoc} .
	op _===_ : Exp&Err Exp&Err -> Exp&Err .
	op _=!=_ : Exp Exp -> Exp {constr prec: 40 l-assoc} .
	op _=!=_ : Exp&Err Exp&Err -> Exp&Err .
	op _<_ : Exp Exp -> Exp {constr prec: 40 l-assoc} .
	op _<_ : Exp&Err Exp&Err -> Exp&Err .
	op _>_ : Exp Exp -> Exp {constr prec: 40 l-assoc} .
	op _>_ : Exp&Err Exp&Err -> Exp&Err .
	op _&&_ : Exp Exp -> Exp {constr prec: 50 l-assoc} .
	op _&&_ : Exp&Err Exp&Err -> Exp&Err .
	op _||_ : Exp Exp -> Exp {constr prec: 55 l-assoc} .
	op _||_ : Exp&Err Exp&Err -> Exp&Err .
}

mod! ENV { pr(PNAT) pr(VAR)
	pr(TABLE(
		K <= view from TRIV to VAR { sort Elt -> Var },
		V <= view from TRIV-ERR-IF to PNAT { sort Elt -> PNat, sort Err -> ErrPNat, sort Elt&Err -> PNat&Err, op err -> errPNat, op (if_then{_}else{_}) -> (if_then{_}else{_}) })
	* { sort Table -> Env, sort EmpTable -> EmpEnv, sort NeTable -> NeEnv, sort ErrTable -> ErrEnv, sort Table&Err -> Env&Err, op errTable -> errEnv, op empTable -> empEnv })
}

mod! STM { pr(EXP)
	[Stm ErrStm < Stm&Err]
	
	op errStm : -> ErrStm {constr} .
	op estm : -> Stm {constr} .
	op _:=_; : Var Exp -> Stm {constr} .
	op _:=_; : Var Exp&Err -> Stm&Err .
	op if_{_}else{_} : Exp Stm Stm -> Stm {constr} .
	op if_{_}else{_} : Exp&Err Stm&Err Stm&Err -> Stm&Err .
	op while_{_} : Exp Stm -> Stm .
	op while_{_} : Exp&Err Stm&Err -> Stm&Err .
	-- op for_ _ _{_} : Var Exp Exp Stm -> Stm {constr} .
	-- op for_ _ _{_} : Var&Err Exp&Err Exp&Err Stm&Err -> Stm&Err .
	op _ _ : Stm Stm -> Stm {constr} .
	op _ _ : Stm&Err Stm&Err -> Stm&Err .
}

mod! INTER { pr(PNAT) pr(EXP) pr(ENV) pr(STM)
	op interpret : Stm -> Env&Err .
	op interpret : Stm&Err -> Env&Err .
	op eval : Stm&Err Env&Err -> Env&Err .
	op evalExp : ExpPNat Env -> PNat .
	op evalExp : Exp&Err Env&Err -> PNat&Err .
	op evalExp : Exp ErrEnv -> ErrPNat .
	op evalIf : PNat&Err Stm&Err Stm&Err Env&Err -> Env&Err .
	op evalWhile : PNat&Err Exp&Err Stm&Err Env&Err -> Env&Err .
	
	-- equations
	var N : PNat . var EN : ExpPNat . vars E E1 E2 : Exp .
	var V : Var . var EV : Env . vars S S1 S2 : Stm . var EE : Env&Err .
	eq interpret(S) = eval(S, empEnv) .							-- (i)
	
	eq eval(S, errEnv) = errEnv .
	eq eval(errStm, EV) = errEnv .
	eq eval(estm, EV) = EV .									-- (iE)
	eq eval((V := E ;), EV) = update(EV,V,evalExp(E,EV)) .		-- (iA)
	eq eval(if E { S1 } else { S2 }, EV) = evalIf(evalExp(E, EV), S1, S2, EV) .	-- (iI) 
	eq eval(while E { S }, EV) = evalWhile(evalExp(E, EV), E, S, EV) .	-- (iI)
	-- eq eval(for V E1 E2 {S}, EV) = eval(V := E1; while (V < E2 || V === E2) { S V := V + n(1); }, EV)  .	-- (iF)
	eq eval(S1 S2, EV) = eval(S2, eval(S1, EV)) .				-- (iC)
	
	eq evalExp(E, errEnv) = errPNat .
	eq evalExp(0, EV) = 0 .
	eq evalExp(V, EV) = lookup(EV,V) .
	eq evalExp(s(EN),EV) = s(evalExp(EN,EV)) .
	eq evalExp(E1 + E2,EV) = evalExp(E1,EV) + evalExp(E2,EV) .		-- (iAd)
	eq evalExp(E1 - E2,EV) = sd(evalExp(E1,EV),evalExp(E2,EV)) .	-- (iMi)
	eq evalExp(E1 * E2,EV) = evalExp(E1,EV) * evalExp(E2,EV) .		-- (iMu)
	eq evalExp(E1 / E2,EV) = evalExp(E1,EV) quo evalExp(E2,EV) .	-- (iDi)
	eq evalExp(E1 % E2,EV) = evalExp(E1,EV) rem evalExp(E2,EV) .	-- (iMo)
	
	eq evalExp(E1 === E2,EV) = if (evalExp(E1,EV) = errPNat or evalExp(E2,EV) = errPNat) then { errPNat } else { if evalExp(E1,EV) = evalExp(E2,EV) then { s(0) } else { 0 } } .
	eq evalExp(E1 =!= E2,EV) = if (evalExp(E1,EV) = errPNat or evalExp(E2,EV) = errPNat) then { errPNat } else { if evalExp(E1,EV) = evalExp(E2,EV) then { 0 } else { s(0) } } .
	
	eq evalExp(E1 < E2,EV) = if (evalExp(E1,EV) = errPNat or evalExp(E2,EV) = errPNat) then { errPNat } else { if evalExp(E1,EV) < evalExp(E2,EV) then { s(0) } else { 0 } } .
	
	eq evalExp(E1 > E2,EV) = if (evalExp(E1,EV) = errPNat or evalExp(E2,EV) = errPNat) then { errPNat } else { if evalExp(E2,EV) < evalExp(E1,EV) then { s(0) } else { 0 } } .
	
	eq evalExp(E1 || E2,EV) = if (evalExp(E1,EV) = errPNat or evalExp(E2,EV) = errPNat) then { errPNat } else { if (evalExp(E1,EV) = s(0) or evalExp(E2,EV) = s(0)) then { s(0) } else { 0 } } .
	eq evalExp(E1 && E2,EV) = if (evalExp(E1,EV) = errPNat or evalExp(E2,EV) = errPNat) then { errPNat } else { if (evalExp(E1,EV) = s(0) and evalExp(E2,EV) = s(0)) then { s(0) } else { 0 } } .
	
	eq evalIf(errPNat, S1, S2, EV) = errEnv .
	eq evalIf(N, S1, S2, EV) = if (0 < N) then { eval(S1, EV) } else { eval(S2, EV) } . -- (evIf)
	
	eq evalWhile(errPNat, E, S, EV) = errEnv .
	eq evalWhile(N, E, S, EV) = if (0 < N) then { eval(while E { S }, eval(S, EV)) } else { EV } . -- (evWh)
}

mod! INSTR principal-sort Instr {
	pr(PNAT) pr(VAR)
	[Instr ErrInstr < Instr&Err]
	op errInstr : -> ErrInstr {constr} .
	op push : PNat -> Instr {constr} .
	op push : ErrPNat -> ErrInstr .
	op load : Var -> Instr {constr} .
	op store : Var -> Instr {constr} .
	op add : -> Instr {constr} .
	op minus : -> Instr {constr} .
	op mult : -> Instr {constr} .
	op div : -> Instr {constr} .
	op mod : -> Instr {constr} .
	op lessThan : -> Instr {constr} .
	op greaterThan : -> Instr {constr} .
	op equal : -> Instr {constr} .
	op notEqual : -> Instr {constr} .
	op and : -> Instr {constr} .
	op or : -> Instr {constr} .
	op jumpOnCond : PNat -> Instr {constr} .
	op jumpOnCond : ErrPNat -> ErrInstr .
	op bjump : PNat -> Instr {constr} .
	op bjump : ErrPNat -> ErrInstr .
	op jump : PNat -> Instr {constr} .
	op jump : ErrPNat -> ErrInstr .
	op quit : -> Instr {constr} .
}

mod! LIST (E :: TRIV-ERR) principal-sort List { pr(PNAT)
	[List ErrList < List&Err]
	[Nil NnList < List]
	op nil : -> Nil {constr} .
	op errList : -> ErrList {constr} .
	
	op _|_ : Elt.E List -> NnList {constr} .
	op _|_ : Elt&Err.E List&Err -> List&Err .
	op _|_ : Err.E List&Err -> ErrList .
	op _|_ : Elt&Err.E ErrList -> ErrList .
	
	op _@_ : List List -> List {assoc} .
	op _@_ : List&Err List&Err -> List&Err .
	op hd : NnList -> Elt.E .
	op hd : Nil -> Err.E .
	op hd : List&Err -> Elt&Err.E .
	op len : List -> PNat .
	op len : List&Err -> PNat&Err .
	
	var E : Elt.E .
	vars L1 L2 : List .
	-- hd
	eq hd(errList) = err .
	eq hd(nil) = err .
	eq hd(E | L1) = E .
	-- _@_
	eq nil @ L2 = L2 .
	eq (E | L1) @ L2 = E | (L1 @ L2) .
	-- len
	eq len(errList) = errPNat .
	eq len(nil) = 0 .
	eq len(E | L1) = s(len(L1)) .
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
	
	op vm : IList&Err -> Env&Err .
	op exec : IList&Err PNat&Err Stack&Err Env&Err -> Env&Err .
	op exec2 : Instr&Err IList&Err PNat&Err Stack&Err Env&Err -> Env&Err {strat (0 1 2 3 4 5 0)} .
	
	op nth : PNat IList -> Instr&Err .
	op nth : PNat&Err IList&Err -> Instr&Err .
	
	op evalEq : PNat&Err PNat&Err -> PNat&Err .
	op evalIneq : PNat&Err PNat&Err -> PNat&Err .
	op evalLessThan : PNat&Err PNat&Err -> PNat&Err .
	op evalGreaterThan : PNat&Err PNat&Err -> PNat&Err .
	op evalAnd : PNat&Err PNat&Err -> PNat&Err .
	op evalOr : PNat&Err PNat&Err -> PNat&Err .
	
	-- equations
	var IL : IList . var ILE : IList&Err . var Stk : Stack&Err . var SE : Stack&Err . var I : Instr . var IE : Instr&Err . vars PC N N1 N2 : PNat . vars NE NE1 NE2 : PNat&Err . var V : Var . var EV : Env . var EE : Env&Err .
	
	eq nth(errPNat, ILE) = errInstr .		-- (nthE1)
	eq nth(N, errIList) = errInstr .		-- (nthE2)
	eq nth(N, iln) = errInstr .				-- (nthE3)
	eq nth(0, I | IL) = I .					-- (nth0)
	eq nth(s(N), I | IL) = nth(N, IL) .		-- (nth)
	
	eq vm(IL) = exec(IL, 0, empstk, empEnv) .				-- (vm)
	eq exec(IL, PC, Stk, EV) = exec2(nth(PC, IL), IL, PC, Stk, EV) .	-- (ex)
	eq exec(ILE, PC, SE, errEnv) = errEnv .
	eq exec(ILE, PC, errStack, EV) = errEnv .
	eq exec(iln, PC, Stk, EV) = errEnv .
	
	-- exec2
		eq exec2(I, ILE, PC, SE, errEnv) = errEnv .				-- (eErr)
		eq exec2(errInstr, ILE, PC, SE, EE) = errEnv .			-- (eErr)
		
		eq exec2(push(N), IL, PC, Stk, EV) = exec(IL, s(PC), N | Stk, EV) .						-- (ePu)
		eq exec2(load(V), IL, PC, Stk, EV) = exec(IL, s(PC), lookup(EV,V) | Stk, EV) .			-- (eLo)
		eq exec2(store(V), IL, PC, empstk, EV) = errEnv .
		eq exec2(store(V), IL, PC, NE | Stk, EV) = exec(IL, s(PC), Stk, update(EV,V,NE)) .		-- (eSt)
		
		eq exec2(add, IL, PC, empstk, EV) = errEnv .
		eq exec2(add, IL, PC, NE | empstk, EV) = errEnv .
		eq exec2(add, IL, PC, NE2 | NE1 | Stk, EV) = exec(IL, s(PC), NE1 + NE2 | Stk, EV) .		-- (eAd)
		
		eq exec2(minus, IL, PC, empstk, EV) = errEnv .
		eq exec2(minus, IL, PC, NE | empstk, EV) = errEnv .
		eq exec2(minus, IL, PC, NE2 | NE1 | Stk, EV) = exec(IL, s(PC), sd(NE1,NE2) | Stk, EV) .	-- (eMi)
		
		eq exec2(mult, IL, PC, empstk, EV) = errEnv .
		eq exec2(mult, IL, PC, NE1 | empstk, EV) = errEnv .
		eq exec2(mult, IL, PC, NE2 | NE1 | Stk, EV) = exec(IL, s(PC), NE1 * NE2 | Stk, EV) .	-- (eMu)
		
		eq exec2(div, IL, PC, empstk, EV) = errEnv .
		eq exec2(div, IL, PC, NE | empstk, EV) = errEnv .
		eq exec2(div, IL, PC, NE2 | NE1 | Stk, EV) = exec(IL, s(PC), NE1 quo NE2 | Stk, EV) .	-- (eDi)
		
		eq exec2(mod, IL, PC, empstk, EV) = errEnv .
		eq exec2(mod, IL, PC, NE | empstk, EV) = errEnv .
		eq exec2(mod, IL, PC, NE2 | NE1 | Stk, EV) = exec(IL, s(PC), NE1 rem NE2 | Stk, EV) .	-- (eMo)
		
		eq exec2(lessThan,IL,PC,empstk,EV) = errEnv .
		eq exec2(lessThan,IL,PC,NE | empstk ,EV) = errEnv .
		eq exec2(lessThan,IL,PC,NE2 | NE1 | Stk,EV) = exec(IL, s(PC), evalLessThan(NE1,NE2) | Stk, EV) .
		
		eq exec2(greaterThan,IL,PC,empstk,EV) = errEnv .
		eq exec2(greaterThan,IL,PC,NE | empstk ,EV) = errEnv .
		eq exec2(greaterThan,IL,PC,NE2 | NE1 | Stk,EV) = exec(IL, s(PC), evalGreaterThan(NE1,NE2) | Stk, EV) .
		
		eq exec2(equal,IL,PC,empstk,EV) = errEnv .
		eq exec2(equal,IL,PC,NE | empstk ,EV) = errEnv .
		eq exec2(equal,IL,PC,NE2 | NE1 | Stk,EV) = exec(IL, s(PC), evalEq(NE1,NE2) | Stk, EV) .
		
		eq exec2(notEqual,IL,PC,empstk,EV) = errEnv .
		eq exec2(notEqual,IL,PC,NE | empstk ,EV) = errEnv .
		eq exec2(notEqual,IL,PC,NE2 | NE1 | Stk,EV) = exec(IL, s(PC), evalIneq(NE1,NE2) | Stk, EV) .
		
		eq exec2(and,IL,PC,empstk,EV) = errEnv .
		eq exec2(and,IL,PC,NE | empstk ,EV) = errEnv .
		eq exec2(and,IL,PC,NE2 | NE1 | Stk,EV) = exec(IL, s(PC), evalAnd(NE1,NE2) | Stk, EV) .
		
		eq exec2(or,IL,PC,empstk,EV) = errEnv .
		eq exec2(or,IL,PC,NE | empstk ,EV) = errEnv .
		eq exec2(or,IL,PC,NE2 | NE1 | Stk,EV) = exec(IL, s(PC), evalOr(NE1,NE2) | Stk, EV) .
		
		eq exec2(jump(N), IL, PC, Stk, EV) = exec(IL, PC + N, Stk, EV) .	-- (eJmp)
		eq exec2(bjump(0),IL,PC,Stk,EV) = exec(IL,PC,Stk,EV) .
		eq exec2(bjump(s(N)),IL,0,Stk,EV) = errEnv .
		eq exec2(bjump(s(N)),IL,s(PC),Stk,EV) = exec2(bjump(N),IL,PC,Stk,EV) .	-- (eBjmp)
		
		eq exec2(jumpOnCond(N), IL, PC, empstk, EV) = errEnv .
		eq exec2(jumpOnCond(N), IL, PC, NE | Stk, EV) = if (NE = 0) then { exec(IL, s(PC), Stk, EV) } else { exec(IL, PC + N, Stk, EV) } .	-- (eJC)
		
		eq exec2(quit, IL, PC, Stk, EE) = EE .													-- (eQ)
		--
		eq evalEq(errPNat, N) = errPNat .	
		eq evalEq(NE, errPNat) = errPNat .	
		eq evalEq(N1, N2) = if (N1 = N2) then {s(0)} else {0} .
		
		eq evalIneq(errPNat, N) = errPNat .	
		eq evalIneq(NE, errPNat) = errPNat .	
		eq evalIneq(N1, N2) = if (N1 = N2) then {0} else {s(0)} .	
		
		eq evalLessThan(errPNat, N) = errPNat .	
		eq evalLessThan(NE, errPNat) = errPNat .
		eq evalLessThan(N1, N2) = if N1 < N2 then {s(0)} else {0} .	
		
		eq evalGreaterThan(errPNat, N) = errPNat .	
		eq evalGreaterThan(NE, errPNat) = errPNat .
		eq evalGreaterThan(N1, N2) = if N2 < N1 then {s(0)} else {0} .
		
		eq evalOr(errPNat, N) = errPNat .
		eq evalOr(NE, errPNat) = errPNat .
		eq evalOr(N1, N2) = if (N1 = s(0) or N2 = s(0)) then {s(0)} else {0} .
		
		eq evalAnd(errPNat, N) = errPNat .
		eq evalAnd(NE, errPNat) = errPNat .
		eq evalAnd(N1, N2) = if (N1 = s(0) and N2 = s(0)) then {s(0)} else {0} .
		
}

mod! COMP { pr(EXP) pr(ILIST) pr(STM)
	op comp : Stm -> IList .
	op comp : Stm&Err -> IList&Err .
	op gen : Stm -> IList .
	op gen : Stm&Err -> IList&Err .
	op genExp : Exp -> IList .
	op genExp : Exp&Err -> IList&Err .
	op en2n : ExpPNat -> PNat .
	
	-- equations
	var EN : ExpPNat . vars E E1 E2 : Exp .
	var V : Var . vars S S1 S2 : Stm .
	eq comp(errStm) = errIList .						-- (cErr)
	eq comp(S) = gen(S) @ (quit | iln) .				-- (c)
	
	eq gen(errStm) = errIList .							-- (cErr2)
	eq gen(estm) = iln .								-- (cE)
	eq gen(V := E ;) = genExp(E) @ (store(V) | iln) .	-- (cA)
	eq gen(if E { S1 } else { S2 }) = genExp(E) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(S1))))) | (gen(S1) @ (jump(s(len(gen(S2)))) | gen(S2))))) .	-- (cI)
	eq gen(while E {S}) = genExp(E) @ ((jumpOnCond(s(s(0))) | jump(s(s(len(gen(S))))) | gen(S)) @ (bjump(s(s(len(gen(S)) + len(genExp(E))))) | iln)) .	-- (cW)
	-- eq gen(for V E1 E2 {S}) = gen(V := E1 ; while (V < E2 || V === E2) { S V := s(V) ;} ) .	-- (cF)
	eq gen(S1 S2) = gen(S1) @ gen(S2) .					-- (cC)
	
	eq en2n(0) = 0 .
	eq en2n(s(EN)) = s(en2n(EN)) .
	eq genExp(errExp) = errIList .
	eq genExp(EN) = push(en2n(EN)) | iln .
	eq genExp(V) = load(V) | iln .
	eq genExp(E1 + E2) = genExp(E1) @ genExp(E2) @ (add | iln) .	-- (gAd)
	eq genExp(E1 - E2) = genExp(E1) @ genExp(E2) @ (minus | iln) .	-- (gMi)
	eq genExp(E1 * E2) = genExp(E1) @ genExp(E2) @ (mult | iln) .	-- (gMu)
	eq genExp(E1 / E2) = genExp(E1) @ genExp(E2) @ (div | iln) .	-- (gDi)
	eq genExp(E1 % E2) = genExp(E1) @ genExp(E2) @ (mod | iln) .	-- (gMo)
	
	eq genExp(E1 === E2) = (genExp(E1) @ genExp(E2)) @ (equal | iln) .
	eq genExp(E1 =!= E2) = (genExp(E1) @ genExp(E2)) @ (notEqual | iln) .
	eq genExp(E1 > E2) = (genExp(E1) @ genExp(E2)) @ (greaterThan | iln) .
	eq genExp(E1 < E2) = (genExp(E1) @ genExp(E2)) @ (lessThan | iln) .
	eq genExp(E1 && E2) = (genExp(E1) @ genExp(E2)) @ (and | iln) .
	eq genExp(E1 || E2) = (genExp(E1) @ genExp(E2)) @ (or | iln) .
}

mod! VERIFY-COMP {
	pr(COMP)
	pr(INTER)
	pr(VM)
	
	op th : Stm -> Bool .
	op th1 : Var Exp -> Bool .
	
	op lem0 : IList IList -> Bool .
	op lemPev : ExpPNat Env&Err -> Bool .
	op lemIln : IList -> Bool .
	
	op lem1E-0 : Exp IList Stack&Err Env&Err -> Bool .
	op lem1E : Exp IList IList Stack&Err Env&Err -> Bool .
	op lem1S : Stm IList IList Stack&Err Env&Err -> Bool .
	
	op lem2 : PNat IList IList PNat Stack&Err Env&Err -> Bool .
	op lem2-0 : IList IList PNat Stack&Err Env&Err -> Bool .
	
	op lemX-0 : IList IList&Err -> Bool .
	op lemX-1 : IList IList&Err -> Bool .
	op lemY-0 : IList Instr -> Bool .
	op lemY-1 : IList Instr Exp -> Bool .
	op lemY-2 : IList Instr Exp Exp -> Bool .
	
	vars E E1 E2 : Exp . var EN : ExpPNat . var V : Var . var S : Stm . vars K N M PC : PNat . vars I I1 I2  : Instr . vars NE NE1 NE2 : PNat&Err .
	vars IL IL1 IL2 : IList . var Stk : Stack . var SE : Stack&Err . var EV : Env . var EE : Env&Err .
	
	eq th(S) = (interpret(S) = vm(comp(S))) .
	eq th1(V, E) = (interpret(V := E ;) = vm(comp(V := E ;))) .
	
	eq lem0(IL1, IL2) = (len(IL1) + len(IL2) = len(IL1 @ IL2)) .
	
	-- lemma Pev : Pnat EValuation
	eq lemPev(EN, EV) = (evalExp(EN, EV) = en2n(EN)) .
	
	-- lemma Iln : Appending iln
	eq lemIln(IL) = (IL @ iln = IL) .
	
	-- lemma 1 : Executing an sublist of instructions
	eq lem1E-0(E, IL, SE, EE) = (exec(genExp(E) @ IL, 0, SE, EE) = exec(genExp(E) @ IL, len(genExp(E)), evalExp(E, EE) | SE, EE)) .
	eq lem1E(E, IL1, IL2, SE, EE) = (exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(E) @ IL2, len(IL1) + len(genExp(E)), evalExp(E, EE) | SE, EE)) .
	eq lem1S(S, IL1, IL2, SE, EE) = (exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE))) .
	
	-- lemma 2
	eq lem2(N, IL1, IL, PC, SE, EE) = (exec2(bjump(len(IL1) + N),IL,len(IL1) + PC,SE,EE) = exec2(bjump(N),IL,PC,SE,EE)) .
	eq lem2-0(IL1, IL, PC, SE, EE) = (exec2(bjump(len(IL1)),IL,PC + len(IL1),SE,EE) = exec2(bjump(0),IL,PC,SE,EE)) .
	
	-- lemma X : nth evaluation with sublist
	eq lemX-0(IL1, IL2) = (nth(len(IL1), IL1 @ IL2) = nth(0, IL2)) .
	eq lemX-1(IL1, IL2) = (nth(s(len(IL1)), IL1 @ IL2) = nth(s(0), IL2)) .
	
	-- lemma Y : (List + Instr) length evaluation
	eq lemY-0(IL, I) = (len(IL @ (I | iln)) = s(len(IL))) .
	eq lemY-1(IL, I, E) = (len(IL @ genExp(E) @ (I | iln)) = s(len(IL @ genExp(E)))) .
	eq lemY-2(IL, I, E1, E2) = (len(IL @ genExp(E1) @ genExp(E2) @ (I | iln)) = s(len(IL @ genExp(E1) @ genExp(E2)))) .
	
	
	-- termination conditional
	op tc : Exp Stm Env PNat -> Bool .
	eq tc(E, S, EV, N) = ((K < N) implies evalExp(E, eval(K, S, EV)) = s(0) and evalExp(E, eval(N, S, EV)) = 0) .
}
