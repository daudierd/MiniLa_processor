in calculator.mod
in eval.mod
in del.mod

-- ----------
-- LEMMA 4 --
-- ----------

-- tc(e, s, ev, n) implies exec(gen(while e {s}) @ (quit | iln), 0, empstk, ev) = eval(n, s, ev) .

-- BASE CASE
open VERIFY-COMP .
	pr(EVAL)
	pr(DEL)
	op e : -> Exp .
	op s : -> Stm .
	op ev : -> Env .
	
	-- Termination Hypothesis
	eq evalExp(e,ev) = 0 .
	
	-- lemma 1E-0
	eq exec(genExp(E) @ IL2, 0, SE, EE) = exec(genExp(E) @ IL2, len(genExp(E)), evalExp(E, EE) | SE, EE) .

	-- Nth-del theorem
	eq nth(N, IL) = hd(del(N, IL)) .
	
	-- check
	red exec(gen(while e {s}) @ (quit | iln), 0, empstk, ev) = eval(0, s, ev) .
close

-- INDUCTION CASE
open VERIFY-COMP .
	pr(EVAL)
	pr(DEL)
	ops n m k : -> PNat .
	op e : -> Exp .
	op s : -> Stm .
	ops ev ev1 : -> Env .
	
	-- Termination hypothesis
	ceq evalExp(e,eval(K, s, ev)) = s(0) if (K < s(n)) .
	eq evalExp(e,eval(s(n), s, ev)) = 0 .
	
	-- Induction Hypothesis
		-- check predicate tc(e,s,eval(s,ev),n) 
		eq (k < n) = true .
		red evalExp(e,eval(k, s, eval(s,ev))) = s(0) .
		red evalExp(e,eval(n, s, eval(s,ev))) = 0 .
		-- then ih(e,s,eval(s,ev),n) can be used
		eq exec(gen(while e {s}) @ (quit | iln), 0, empstk, eval(s,ev)) = eval(n, s, eval(s,ev)) .
	
	-- lemma 0
		eq len(IL2 @ IL1) = len(IL1) + len(IL2) .
	
	-- lemma 1E-0
	eq exec(genExp(E) @ IL2, 0, SE, EE) = exec(genExp(E) @ IL2, len(genExp(E)), evalExp(E, EE) | SE, EE) .

	-- Nth-del theorem
	eq nth(N, IL) = hd(del(N, IL)) .
	
	-- lemma 1S (version with exec2)
	eq exec2(nth(0,gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec2(nth(0,IL2), IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
	-- lemma 1S (version with exec2 and hd)
	eq exec2(hd(gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec2(nth(0,IL2), IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
	
	-- lemma 2
	eq exec2(bjump(len(IL1) + N),IL,len(IL1) + PC,SE,EE) = exec2(bjump(N),IL,PC,SE,EE) .
	eq exec2(bjump(len(IL1)),IL,PC + len(IL1),SE,EE) = exec2(bjump(0),IL,PC,SE,EE) .
		-- when PC = 0
		eq exec2(bjump(len(IL1)),IL,len(IL1),SE,EE) = exec2(bjump(0),IL,0,SE,EE) .
	
	-- rewriting evalExp(e,ev)
		red evalExp(e,ev) = evalExp(e,eval(0, s, ev)) .
		red 0 < s(n) .
		-- provided two previous scores are true:
		eq evalExp(e,ev) = s(0) .
	
	-- check
	-- red exec(gen(while e {s}) @ (quit | iln), 0, empstk, ev) .
	-- = eval(n, s, ev) .
		op pca : -> PNat .
		ops ila il1b il2b : -> IList .
		
		eq pca = s(s(len(genExp(e)))) .
		eq ila = (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s))))) | (gen(s) @ (bjump(s(s((len(gen(s)) + len(genExp(e)))))) | (quit | iln)))))) .
		
		eq il1b = (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s))))) | iln))) .
		
		eq il2b = (bjump(s(s((len(genExp(e)) + len(gen(s)))))) | (quit | iln)) .
		
	-- phase 1 : LHS = f(X)
		red exec(gen(while e {s}) @ (quit | iln), 0, empstk, ev) = exec2(hd(gen(s) @ il2b),ila,pca,empstk,ev) .
		
	-- phase 2 : X = Y
		red ila = il1b @ gen(s) @ il2b .
		red len(il1b) = pca .
		
	-- phase 3 : f(Y) = Z
		eq eval(s,ev) = ev1 .
		red exec2(hd(gen(s) @ il2b), il1b @ gen(s) @ il2b, len(il1b), empstk, ev) = exec(gen(while e {s}) @ (quit | iln), 0, empstk, eval(s,ev)) .
		
	-- phase 4 : ih(e,s,eval(s,ev),n) : Z = Z'
			eq exec(gen(while e {s}) @ (quit | iln), 0, empstk, eval(s,ev)) = eval(n, s, eval(s,ev)) .

		-- red exec(gen(while e {s}) @ (quit | iln), 0, empstk, eval(s,ev)) = eval(n, s, eval(s,ev)).
		red exec(gen(while e {s}) @ (quit | iln), 0, empstk, eval(s,ev)) .
		
	-- phase 5 : Z' = RHS
		red eval(n, s, eval(s,ev)) = eval(s(n), s, ev) .
close