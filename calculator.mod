-- ----------------------------------------------------------
--                                                         --
--       MiniLa language processor verified compiler       --
--                      SPECIFICATION                      --
--                                                         --
--                     DAUDIER, Dorian                     --
--            Special research student at JAIST            --
--                                                         --
-- ----------------------------------------------------------

-- This file contains the specifications for the MiniLa Language Processor
-- The code is organized as follows:
	-- Primitive definitions: variables, expressions, environment, statements, instructions, stack, ...
	-- Interpreter
	-- Virtual Machine
	-- Compiler
	-- A module dedicated to verification of the correctness, used in proof scores

-- The proof scores used to demonstrate the compiler correctness are located in the following files:
	-- calculator-verif.mod (This is the main file)
	-- lem1.mod
	-- lemXY.mod
	-- nth-del.mod (for using del operator in rewrites)

in table.mod
in pnat.mod

-- ------------------------
-- PRIMITIVE DEFINITIONS --
-- ------------------------

-- VARIABLES IN MINILA
mod! VAR principal-sort Var {
	[Var]
}

-- MINILA EXPRESSIONS
mod! EXP {
	pr(VAR)
	[Var ExpPNat < Exp]
	[Exp ErrExp < Exp&Err]
	op errExp : -> ErrExp {constr} .
	-- constructors
	op 0 : -> ExpPNat {constr} .
	op s : ExpPNat -> ExpPNat {constr} .
	
	-- operations on natural numbers
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

-- EXECUTION ENVIRONMENT
mod! ENV { pr(PNAT) pr(VAR)
	pr(TABLE(
		K <= view from TRIV to VAR { sort Elt -> Var },
		V <= view from TRIV-ERR-IF to PNAT { sort Elt -> PNat, sort Err -> ErrPNat, sort Elt&Err -> PNat&Err, op err -> errPNat, op (if_then{_}else{_}) -> (if_then{_}else{_}) })
	* { sort Table -> Env, sort EmpTable -> EmpEnv, sort NeTable -> NeEnv, sort ErrTable -> ErrEnv, sort Table&Err -> Env&Err, op errTable -> errEnv, op empTable -> empEnv })
}

-- STATEMENTS
mod! STM { pr(EXP)
	[Stm]
	
	op estm : -> Stm {constr} .
	op _:=_; : Var Exp -> Stm {constr} .
	op if_{_}else{_} : Exp Stm Stm -> Stm {constr} .
	op _ _ : Stm Stm -> Stm {constr} .
}

-- INSTRUCTIONS FOR MACHINE CODE
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
	op jump : PNat -> Instr {constr} .
	op jump : ErrPNat -> ErrInstr .
	op quit : -> Instr {constr} .
}

-- GENERIC LIST
mod! LIST (E :: TRIV-ERR) principal-sort List { pr(PNAT)
	[List ErrList < List&Err]
	[Nil NnList < List]
	op nil : -> Nil {constr} .
	op errList : -> ErrList {constr} .
	op _|_ : Elt.E List -> NnList {constr} .
	op _|_ : Elt&Err.E List&Err -> List&Err .
	op len : List -> PNat .
	op len : List&Err -> PNat&Err .
	op hd : NnList -> Elt.E .
	op hd : Nil -> Err.E .
	op hd : List&Err -> Elt&Err.E .
	op _@_ : List List -> List {assoc} .
	op _@_ : List&Err List&Err -> List&Err .
	
	var E : Elt.E .
	vars L1 L2 : List .
	-- _@_
	eq nil @ L2 = L2 .
	eq (E | L1) @ L2 = E | (L1 @ L2) .
	-- hd
	eq hd(errList) = err .
	eq hd(nil) = err .
	eq hd(E | L1) = E .
	-- len
	eq len(errList) = errPNat .
	eq len(nil) = 0 .
	eq len(E | L1) = s(len(L1)) .
}

-- SEQUENCE OF INSTRUCTIONS
-- This is built as a list of instructions, using the generic list definition
mod! ILIST principal-sort IList {
	pr(LIST(E <= view from TRIV-ERR to INSTR {
		sort Elt -> Instr, sort Err -> ErrInstr, sort Elt&Err -> Instr&Err, op err -> errInstr
	}) * {
		sort List -> IList, sort Nil -> Iln, sort NnList -> NnIList, sort ErrList -> ErrIList, sort List&Err -> IList&Err, op nil -> iln, op errList -> errIList })
}

-- STACK
-- This is built as a list of natural numbers, using the generic list definition
mod! STACK {
	pr(LIST(E <= view from TRIV-ERR to PNAT {sort Elt -> PNat, sort Err -> ErrPNat, sort Elt&Err -> PNat&Err, op err -> errPNat}) * {sort List -> Stack, sort ErrList -> ErrStack, sort List&Err -> Stack&Err, op nil -> empstk, op errList -> errStack})
}


-- --------------
-- INTERPRETER --
-- --------------

mod! INTER { pr(PNAT) pr(EXP) pr(ENV) pr(STM)
	op inter : Stm -> Env&Err .
	op eval : Stm Env&Err -> Env&Err .
	op evalExp : ExpPNat Env -> PNat .
	op evalExp : Exp&Err Env&Err -> PNat&Err .
	op evalIf : PNat&Err Stm Stm Env&Err -> Env&Err .
	
	-- EQUATIONS
	var N : PNat . var EN : ExpPNat . vars E E1 E2 : Exp .
	var V : Var . var EV : Env . vars S S1 S2 : Stm . var EE : Env&Err .
	eq inter(S) = eval(S, empEnv) .
	
	-- 1ST REFINEMENT: eval
	eq eval(S, errEnv) = errEnv .
	eq eval(estm, EV) = EV .
	eq eval((V := E ;), EV) = update(EV,V,evalExp(E,EV)) .
	eq eval(if E { S1 } else { S2 }, EV) = evalIf(evalExp(E, EV), S1, S2, EV) .
	eq eval(S1 S2, EV) = eval(S2, eval(S1, EV)) .
	
	-- 2ND REFINEMENT: evalExp
	eq evalExp(E, errEnv) = errPNat .
	eq evalExp(0, EV) = 0 .
	eq evalExp(V, EV) = lookup(EV,V) .
	eq evalExp(s(EN),EV) = s(evalExp(EN,EV)) .
	eq evalExp(E1 + E2,EV) = evalExp(E1,EV) + evalExp(E2,EV) .
	eq evalExp(sd(E1,E2),EV) = sd(evalExp(E1,EV),evalExp(E2,EV)) .
	eq evalExp(E1 * E2,EV) = evalExp(E1,EV) * evalExp(E2,EV) .
	eq evalExp(E1 / E2,EV) = evalExp(E1,EV) quo evalExp(E2,EV) .
	eq evalExp(E1 % E2,EV) = evalExp(E1,EV) rem evalExp(E2,EV) .
	
	eq evalExp(E1 === E2,EV) = if (evalExp(E1,EV) = errPNat or evalExp(E2,EV) = errPNat) then { errPNat } else { if evalExp(E1,EV) = evalExp(E2,EV) then { s(0) } else { 0 } } .
	eq evalExp(E1 =!= E2,EV) = if (evalExp(E1,EV) = errPNat or evalExp(E2,EV) = errPNat) then { errPNat } else { if evalExp(E1,EV) = evalExp(E2,EV) then { 0 } else { s(0) } } .
	
	eq evalExp(E1 < E2,EV) = if (evalExp(E1,EV) = errPNat or evalExp(E2,EV) = errPNat) then { errPNat } else { if evalExp(E1,EV) < evalExp(E2,EV) then { s(0) } else { 0 } } .
	
	eq evalExp(E1 > E2,EV) = if (evalExp(E1,EV) = errPNat or evalExp(E2,EV) = errPNat) then { errPNat } else { if evalExp(E2,EV) < evalExp(E1,EV) then { s(0) } else { 0 } } .
	
	eq evalExp(E1 || E2,EV) = if (evalExp(E1,EV) = errPNat or evalExp(E2,EV) = errPNat) then { errPNat } else { if (evalExp(E1,EV) = s(0) or evalExp(E2,EV) = s(0)) then { s(0) } else { 0 } } .
	eq evalExp(E1 && E2,EV) = if (evalExp(E1,EV) = errPNat or evalExp(E2,EV) = errPNat) then { errPNat } else { if (evalExp(E1,EV) = s(0) and evalExp(E2,EV) = s(0)) then { s(0) } else { 0 } } .
	
		-- evalIf
		eq evalIf(errPNat, S1, S2, EV) = errEnv .
		eq evalIf(N, S1, S2, EV) = if (0 < N) then { eval(S1, EV) } else { eval(S2, EV) } .
}


-- ------------------
-- VIRTUAL MACHINE --
-- ------------------

mod! VM {
	pr(ILIST)
	pr(STACK)
	pr(ENV)
	op vm : IList&Err -> Env&Err .
	op exec : IList&Err PNat&Err Stack&Err Env&Err -> Env&Err .
	op exec2 : Instr&Err IList&Err PNat&Err Stack&Err Env&Err -> Env&Err .
	op nth : PNat IList -> Instr .
	op nth : PNat&Err IList&Err -> Instr&Err .
	
	-- EQUATIONS
	var IL : IList . var ILE : IList&Err . vars PC N N1 N2 : PNat . var SE : Stack&Err . var I : Instr . var IE : Instr&Err . vars NE NE1 NE2 : PNat&Err .
	var V : Var . var EV : Env . var EE : Env&Err .
	
	eq vm(IL) = exec(IL, 0, empstk, empEnv) .
	
	-- nth operator to extract pointed instruction
	eq nth(errPNat, ILE) = errInstr .
	eq nth(N, errIList) = errInstr .
	eq nth(N, iln) = errInstr .
	eq nth(0, I | IL) = I .
	eq nth(s(N), I | IL) = nth(N, IL) .
	
	-- 1ST REFINEMENT: exec
	eq exec(IL, PC, SE, EV) = exec2(nth(PC, IL), IL, PC, SE, EV) .
	eq exec(ILE, PC, SE, errEnv) = errEnv .
	eq exec(ILE, PC, errStack, EV) = errEnv .
	eq exec(iln, PC, SE, EV) = errEnv .
	
	-- 2ND REFINEMENT: exec2
	eq exec2(push(N), IL, PC, SE, EV) = exec(IL, s(PC), N | SE, EV) .
	eq exec2(load(V), IL, PC, SE, EV) = exec(IL, s(PC), lookup(EV,V) | SE, EV) .
	eq exec2(store(V), IL, PC, empstk, EV) = errEnv .
	eq exec2(store(V), IL, PC, NE | SE, EV) = exec(IL, s(PC), SE, update(EV,V,NE)) .
	
	eq exec2(quit, IL, PC, SE, EE) = EE .
	
	-- Arithmetic operations
		eq exec2(add, IL, PC, empstk, EV) = errEnv .
		eq exec2(add, IL, PC, NE | empstk, EV) = errEnv .
		eq exec2(add, IL, PC, NE2 | NE1 | SE, EV) = exec(IL, s(PC), NE1 + NE2 | SE, EV) .
		
		eq exec2(minus, IL, PC, empstk, EV) = errEnv .
		eq exec2(minus, IL, PC, NE | empstk, EV) = errEnv .
		eq exec2(minus, IL, PC, NE2 | NE1 | SE, EV) = exec(IL, s(PC), sd(NE1,NE2) | SE, EV) .
		
		eq exec2(mult, IL, PC, empstk, EV) = errEnv .
		eq exec2(mult, IL, PC, NE1 | empstk, EV) = errEnv .
		eq exec2(mult, IL, PC, NE2 | NE1 | SE, EV) = exec(IL, s(PC), NE1 * NE2 | SE, EV) .
		
		eq exec2(div, IL, PC, empstk, EV) = errEnv .
		eq exec2(div, IL, PC, NE | empstk, EV) = errEnv .
		eq exec2(div, IL, PC, NE2 | NE1 | SE, EV) = exec(IL, s(PC), NE1 quo NE2 | SE, EV) .
		
		eq exec2(mod, IL, PC, empstk, EV) = errEnv .
		eq exec2(mod, IL, PC, NE | empstk, EV) = errEnv .
		eq exec2(mod, IL, PC, NE2 | NE1 | SE, EV) = exec(IL, s(PC), NE1 rem NE2 | SE, EV) .
	
	-- Boolean calculus
	-- we use the evaluation subfunctions defined at the end of the module
		eq exec2(lessThan,IL,PC,empstk,EV) = errEnv .
		eq exec2(lessThan,IL,PC,NE | empstk ,EV) = errEnv .
		eq exec2(lessThan,IL,PC,NE2 | NE1 | SE,EV) = exec(IL, s(PC), evalLessThan(NE1,NE2) | SE, EV) .
		
		eq exec2(greaterThan,IL,PC,empstk,EV) = errEnv .
		eq exec2(greaterThan,IL,PC,NE | empstk ,EV) = errEnv .
		eq exec2(greaterThan,IL,PC,NE2 | NE1 | SE,EV) = exec(IL, s(PC), evalGreaterThan(NE1,NE2) | SE, EV) .
		
		eq exec2(equal,IL,PC,empstk,EV) = errEnv .
		eq exec2(equal,IL,PC,NE | empstk ,EV) = errEnv .
		eq exec2(equal,IL,PC,NE2 | NE1 | SE,EV) = exec(IL, s(PC), evalEq(NE1,NE2) | SE, EV) .
		
		eq exec2(notEqual,IL,PC,empstk,EV) = errEnv .
		eq exec2(notEqual,IL,PC,NE | empstk ,EV) = errEnv .
		eq exec2(notEqual,IL,PC,NE2 | NE1 | SE,EV) = exec(IL, s(PC), evalIneq(NE1,NE2) | SE, EV) .
		
		eq exec2(and,IL,PC,empstk,EV) = errEnv .
		eq exec2(and,IL,PC,NE | empstk ,EV) = errEnv .
		eq exec2(and,IL,PC,NE2 | NE1 | SE,EV) = exec(IL, s(PC), evalAnd(NE1,NE2) | SE, EV) .
		
		eq exec2(or,IL,PC,empstk,EV) = errEnv .
		eq exec2(or,IL,PC,NE | empstk ,EV) = errEnv .
		eq exec2(or,IL,PC,NE2 | NE1 | SE,EV) = exec(IL, s(PC), evalOr(NE1,NE2) | SE, EV) .
	
	-- jump instructions
		eq exec2(jump(N), IL, PC, SE, EV) = exec(IL, PC + N, SE, EV) .
		
		eq exec2(jumpOnCond(N), IL, PC, empstk, EV) = errEnv .
		eq exec2(jumpOnCond(N), IL, PC, NE | SE, EV) = if (NE = 0) then { exec(IL, s(PC), SE, EV) } else { exec(IL, PC + N, SE, EV) } .
	
	-- Evaluation subfunctions
	-- They are used to match boolean values with their natural number equivalent (0 for 'false' and s(0) for 'true')
		op evalEq : PNat&Err PNat&Err -> PNat&Err .
		op evalIneq : PNat&Err PNat&Err -> PNat&Err .
		op evalLessThan : PNat&Err PNat&Err -> PNat&Err .
		op evalGreaterThan : PNat&Err PNat&Err -> PNat&Err .
		op evalAnd : PNat&Err PNat&Err -> PNat&Err .
		op evalOr : PNat&Err PNat&Err -> PNat&Err .
		
		-- equations
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


-- -----------
-- COMPILER --
-- -----------

mod! COMP { pr(EXP) pr(ILIST) pr(STM)
	op comp : Stm -> IList .
	op gen : Stm -> IList .
	op genExp : Exp -> IList .
	op en2n : ExpPNat -> PNat .
	
	-- EQUATIONS
	var EN : ExpPNat . vars E E1 E2 : Exp .
	var V : Var . vars S S1 S2 : Stm .
	eq comp(S) = gen(S) @ (quit | iln) .
	
	-- 1ST REFINEMENT: 
	eq gen(estm) = iln .
	eq gen(V := E ;) = genExp(E) @ (store(V) | iln) .
	eq gen(if E { S1 } else { S2 }) = genExp(E) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(S1))))) | (gen(S1) @ (jump(s(len(gen(S2)))) | gen(S2))))) .
	eq gen(S1 S2) = gen(S1) @ gen(S2) .
	
	eq en2n(0) = 0 .
	eq en2n(s(EN)) = s(en2n(EN)) .
	eq genExp(EN) = push(en2n(EN)) | iln .
	eq genExp(V) = load(V) | iln .
	eq genExp(E1 + E2) = genExp(E1) @ genExp(E2) @ (add | iln) .
	eq genExp(sd(E1,E2)) = genExp(E1) @ genExp(E2) @ (minus | iln) .
	eq genExp(E1 * E2) = genExp(E1) @ genExp(E2) @ (mult | iln) .
	eq genExp(E1 / E2) = genExp(E1) @ genExp(E2) @ (div | iln) .
	eq genExp(E1 % E2) = genExp(E1) @ genExp(E2) @ (mod | iln) .
	eq genExp(E1 === E2) = (genExp(E1) @ genExp(E2)) @ (equal | iln) .
	eq genExp(E1 =!= E2) = (genExp(E1) @ genExp(E2)) @ (notEqual | iln) .
	eq genExp(E1 > E2) = (genExp(E1) @ genExp(E2)) @ (greaterThan | iln) .
	eq genExp(E1 < E2) = (genExp(E1) @ genExp(E2)) @ (lessThan | iln) .
	eq genExp(E1 && E2) = (genExp(E1) @ genExp(E2)) @ (and | iln) .
	eq genExp(E1 || E2) = (genExp(E1) @ genExp(E2)) @ (or | iln) .
}


-- ----------------------
-- VERIFICATION MODULE --
-- ----------------------

mod! VERIFY-COMP {
	pr(COMP)
	pr(INTER)
	pr(VM)
	
	vars E E1 E2 : Exp . var EN : ExpPNat . var V : Var . var S : Stm .
	vars IL IL1 IL2 : IList . var I : Instr . var SE : Stack&Err . var EV : Env . var EE : Env&Err .
	
	-- CORRECTNESS OF THE COMPILER
	op th : Stm -> Bool 
	eq th(S) = (inter(S) = vm(comp(S))) .
	
		-- for assignments especially
		op th1 : Var Exp -> Bool .
		eq th1(V, E) = (inter(V := E ;) = vm(comp(V := E ;))) .
	
	-- SUPPORTING LEMMAS
	op lemPev : ExpPNat Env&Err -> Bool .
	op lemLadd : IList IList -> Bool .
	
	eq lemPev(EN, EV) = (evalExp(EN, EV) = en2n(EN)) .
	eq lemLadd(IL1, IL2) = (len(IL1) + len(IL2) = len(IL1 @ IL2)) .
	
	-- LEMMA 1
		-- Rules for rewriting exec calls when processing irreducible generated sublists genExp(E) or gen(S)
		op lem1E-0 : Exp IList Stack&Err Env&Err -> Bool .
		op lem1E : Exp IList IList Stack&Err Env&Err -> Bool .
		op lem1S-0 : Stm IList Stack&Err Env&Err -> Bool .
		op lem1S : Stm IList IList Stack&Err Env&Err -> Bool .
		
		eq lem1E-0(E, IL, SE, EE) = (exec(genExp(E) @ IL, 0, SE, EE) = exec(genExp(E) @ IL, len(genExp(E)), evalExp(E, EE) | SE, EE)) .
		eq lem1E(E, IL1, IL2, SE, EE) = (exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(E) @ IL2, len(genExp(E)) + len(IL1), evalExp(E, EE) | SE, EE)) .
		
		eq lem1S-0(S, IL, SE, EE) = (exec(gen(S) @ IL, 0, SE, EE) = exec(gen(S) @ IL, len(gen(S)), SE, eval(S, EE))) .
		eq lem1S(S, IL1, IL2, SE, EE) = (exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(gen(S)) + len(IL1), SE, eval(S, EE))) .
	
	-- LEMMA X
		-- Simplification of nth(PC, IL1 @ IL2) by identification of the term 'len(IL1)' in PC
		op lemX-0 : IList IList -> Bool .
		op lemX-1 : IList IList -> Bool .
		eq lemX-0(IL1, IL2) = (nth(len(IL1), IL1 @ IL2) = nth(0, IL2)) .
		eq lemX-1(IL1, IL2) = (nth(s(len(IL1)), IL1 @ IL2) = nth(s(0), IL2)) .
	
	-- LEMMA Y
		-- Rewriting the length of a sequence of instructions ending with an orphan instruction
		op lemY-0 : IList Instr -> Bool .
		op lemY-1 : IList Instr Exp -> Bool .
		op lemY-2 : IList Instr Exp Exp -> Bool .
		eq lemY-0(IL, I) = (len(IL @ (I | iln)) = s(len(IL))) .
		eq lemY-1(IL, I, E) = (len(IL @ genExp(E) @ (I | iln)) = s(len(IL @ genExp(E)))) .
		eq lemY-2(IL, I, E1, E2) = (len(IL @ genExp(E1) @ genExp(E2) @ (I | iln)) = s(len(IL @ genExp(E1) @ genExp(E2)))) .
}
