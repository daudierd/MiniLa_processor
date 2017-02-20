in calculator.mod
in del.mod

-- Stm = while E { S }
open VERIFY-COMP .
	pr(DEL)
	op e : -> Exp .
	op s : -> Stm .
	ops il1 il2 : -> IList .
	op ev : -> Env .
	
	-- Reduction hypotheses
	eq evalExp(e,empEnv) = 0 .
	
	-- lemma 0
	eq len(IL1 @ IL2) = len(IL1) + len(IL2) .
	-- lemma 1E-0
	eq exec(genExp(E) @ IL2, 0, SE, EE) = exec(genExp(E) @ IL2, len(genExp(E)), evalExp(E, EE) | SE, EE) .
	-- lemma 1E
	eq exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(E) @ IL2, len(IL1) + len(genExp(E)), evalExp(E, EE) | SE, EE) .
	-- Nth-del theorem
	eq nth(N, IL) = hd(del(N, IL)) .
	
	-- lemma 1S (version with exec2)
	eq exec2(nth(0,gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec2(nth(0,IL2), IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
	
	-- lemma 2
	eq exec2(bjump(len(IL1) + N),IL,len(IL1) + PC,SE,EE) = exec2(bjump(N),IL,PC,SE,EE) .
	eq exec2(bjump(len(IL1)),IL,PC + len(IL1),SE,EE) = exec2(bjump(0),IL,PC,SE,EE) .
		-- when PC = 0
		eq exec2(bjump(len(IL1)),IL,len(IL1),SE,EE) = exec2(bjump(0),IL,0,SE,EE) .
	
	-- check
	red th(while e {s}) .
close