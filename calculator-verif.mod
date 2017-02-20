in calculator.mod
in eval.mod
in del.mod

-- ------------
-- THEOREM 1 --
-- ------------

-- Var = PNat
open VERIFY-COMP .
	op en : -> ExpPNat .
	op v : -> Var .
	
	-- lemma Pev
	eq evalExp(EN, EV) = en2n(EN) .
	-- check
	red th1(v, en) .
close

-- Var = Var
open VERIFY-COMP .
	ops v x : -> Var .
	-- check
	red th1(v, x) .
close

-- Var = Exp
	-- Case splitting on update(empEnv,v,evalExp(e,empEnv))
	open VERIFY-COMP .
		op e : -> Exp .
		op v : -> Var .
		op il : -> IList .
		
		-- Case splitting hypothesis
		eq update(empEnv,v,evalExp(e,empEnv)) = errEnv .
		-- lemma1E-0
		eq exec(genExp(E) @ IL2, 0, SE, EE) = exec(genExp(E) @ IL2, len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- lemma X
		eq nth(len(IL1), IL1 @ IL2) = nth(0, IL2) .
		eq nth(s(len(IL1)), IL1 @ IL2) = nth(s(0), IL2) .
		-- check
		red th1(v, e) .
	close

	open VERIFY-COMP .
		op e : -> Exp .
		op v : -> Var .
		op ev : -> Env .
		
		-- Case splitting hypothesis
		eq update(empEnv,v,evalExp(e,empEnv)) = ev .
		-- lemma 2 (version with IL1 = iln)
		eq exec(genExp(E) @ IL2, 0, SE, EE) = exec(genExp(E) @ IL2, len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- lemma X
		eq nth(len(IL1), IL1 @ IL2) = nth(0, IL2) .
		eq nth(s(len(IL1)), IL1 @ IL2) = nth(s(0), IL2) .
		
		-- check
		red th1(v, e) .
	close
	
-- ----------
-- THEOREM --
-- ----------

-- THEOREM: BASE CASE

-- Stm = estm
open VERIFY-COMP .
	-- check
	red th(estm) .
close

-- Stm = (V := E ;)
open VERIFY-COMP .
	op e : -> Exp .
	op v : -> Var .
	-- check
	red th1(v,e) implies th(v := e ;) .
close

-- Stm = if E { S1 } else { S2 }
	-- CASE 1 : Case splitting, evalExp(e, empEnv) = 0
	open VERIFY-COMP .
		pr(DEL)
		op e : -> Exp .
		ops s1 s2 : -> Stm .
		ops il1 il2 : -> IList .
		
		-- Case splitting : evalExp(e, empEnv) = 0
		eq evalExp(e,empEnv) = 0 .
		
		-- lemma 0
		eq len(IL1 @ IL2) = len(IL1) + len(IL2) .
		-- lemma 1E-0
		eq exec(genExp(E) @ IL2, 0, SE, EE) = exec(genExp(E) @ IL2, len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		
		-- lemma 1S (version with exec2)
		eq exec2(nth(0,gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec2(nth(0,IL2), IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		
		-- check
			op pca : -> PNat .
			ops ila il1b il2b : -> IList .
			
			eq pca = s(s(s((len(gen(s1)) + len(genExp(e)))))) .
			eq ila = (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | (gen(s2) @ (quit | iln))))))) .
			
			eq il1b = genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | iln)))) .
			eq il2b = (quit | iln) .
		-- phase 1 : LHS = f(X)
		red vm(comp(if e {s1} else {s2})) = exec2(nth(0, gen(s2) @ il2b), ila, pca, empstk, empEnv) .
		
		-- phase 2 : X = Y
		red ila = il1b @ gen(s2) @ il2b .
		red len(il1b) = pca .
		
		-- phase 3 : f(Y) = RHS
		red exec2(nth(0, gen(s2) @ il2b), il1b @ gen(s2) @ il2b, len(il1b), empstk, empEnv) = inter(if e {s1} else {s2}) .
	close
	
	-- CASE 2.1 : Case splitting, evalExp(e, empEnv) > 0
	-- eval(s1,empEnv) has no error
	open VERIFY-COMP .
		pr(DEL)
		op e : -> Exp .
		ops s1 s2 : -> Stm .
		ops il1 il2 : -> IList .
		op ev : -> Env .
		
		-- Case splitting : evalExp(e, ev) > 0
		eq evalExp(e,empEnv) = s(N) .
		
		-- lemma 0
		eq len(IL1 @ IL2) = len(IL1) + len(IL2) .
		-- lemma 1E-0
		eq exec(genExp(E) @ IL2, 0, SE, EE) = exec(genExp(E) @ IL2, len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		
		--  modified version of lemma 1S (equality with exec2)
		eq exec2(nth(0,gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec2(nth(0,IL2), IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		
		-- eval(s1,empEnv) is not errEnv
			eq eval(s1,empEnv) = ev .
			
			-- check
				op pca : -> PNat .
				ops ila il1b il2b : -> IList .
				
				eq pca = s(s(len(genExp(e)))) .
				eq ila = genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | (gen(s2) @ (quit | iln)))))) .
				
				eq il1b = genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | iln)) .
				eq il2b = (jump(s(len(gen(s2)))) | (gen(s2) @ (quit | iln))) .
			
			-- phase 1 : LHS = f(X)
			red vm(comp(if e {s1} else {s2})) = exec2(nth(0, gen(s1) @ il2b), ila, pca, empstk, empEnv) .
			
			-- phase 2 : X = Y
			red ila = il1b @ gen(s1) @ il2b .
			red len(il1b) = pca .
			
			-- phase 3 : f(Y) = RHS
			red exec2(nth(0, gen(s1) @ il2b), il1b @ gen(s1) @ il2b, len(il1b), empstk, empEnv) = inter(if e {s1} else {s2}) .
	close
	
	-- CASE 2.2 : Case splitting, evalExp(e, empEnv) > 0
	-- eval(s1,empEnv) has error
	open VERIFY-COMP .
		pr(DEL)
		op e : -> Exp .
		ops s1 s2 : -> Stm .
		ops il1 il2 : -> IList .
		
		-- Case splitting : evalExp(e, empEnv) > 0
		eq evalExp(e,empEnv) = s(N) .
		
		-- lemma 0
		eq len(IL1 @ IL2) = len(IL1) + len(IL2) .
		-- lemma 1E-0
		eq exec(genExp(E) @ IL2, 0, SE, EE) = exec(genExp(E) @ IL2, len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		
		--  modified version of lemma 1S (equality with exec2)
		eq exec2(nth(0,gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec2(nth(0,IL2), IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		
		-- eval(s1,empEnv) is errEnv
			eq eval(s1,empEnv) = errEnv .
			
			-- check
				op pca : -> PNat .
				ops ila il1b il2b : -> IList .
				
				eq pca = s(s(len(genExp(e)))) .
				eq ila = genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | (gen(s2) @ (quit | iln)))))) .
				
				eq il1b = genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | iln)) .
				eq il2b = (jump(s(len(gen(s2)))) | (gen(s2) @ (quit | iln))) .
			
			-- phase 1 : LHS = f(X)
			red vm(comp(if e {s1} else {s2})) = exec2(nth(0, gen(s1) @ il2b), ila, pca, empstk, empEnv) .
			
			-- phase 2 : X = Y
			red ila = il1b @ gen(s1) @ il2b .
			red len(il1b) = pca .
			
			-- phase 3 : f(Y) = RHS
			red exec2(nth(0, gen(s1) @ il2b), il1b @ gen(s1) @ il2b, len(il1b), empstk, empEnv) = inter(if e {s1} else {s2}) .
	close
	
open VERIFY-COMP .
	pr(EVAL)
	op n : -> PNat .
	op e : -> Exp .
	op s : -> Stm .
	
	-- termination condition
		ceq evalExp(e, eval(N, s, empEnv)) = s(0) if (N < n) .
		ceq evalExp(e, eval(N, s, empEnv)) = 0 if (N = n) .
	
	-- lemma 3
		eq eval(while e {s}, empEnv) = eval(n, s, empEnv) .
	-- lemma 4
		eq eval(n, s, empEnv) = exec(gen(while e {s}) @ (quit | iln), 0, empstk, empEnv) .
		
	red th(while e {s}) .
close
eof

-- THEOREM: INDUCTION CASE
	-- case splitting based on eval(s2,eval(s1,empEnv))
	open VERIFY-COMP .
		ops s1 s2 : -> Stm .
		-- lemma 1S
		eq exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		eq exec(gen(S) @ IL2, 0, SE, EE) = exec(gen(S) @ IL2, len(gen(S)), SE, eval(S, EE)) .
		-- lemma X
		eq nth(len(IL1), IL1 @ IL2) = nth(0, IL2) .
		eq nth(s(len(IL1)), IL1 @ IL2) = nth(s(0), IL2) .
		-- IH
		eq inter(s1) = vm(comp(s1)) .
		eq inter(s2) = vm(comp(s2)) .
		
		eq eval(s2,eval(s1,empEnv)) = errEnv .
		
		-- check
		red th(s1 s2) .
	close
	
	open VERIFY-COMP .
		ops s1 s2 : -> Stm .
		op ev : -> Env .
		-- lemma 1S
		eq exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		eq exec(gen(S) @ IL2, 0, SE, EE) = exec(gen(S) @ IL2, len(gen(S)), SE, eval(S, EE)) .
		-- lemma X
		eq nth(len(IL1), IL1 @ IL2) = nth(0, IL2) .
		-- IH
		eq inter(s1) = vm(comp(s1)) .
		eq inter(s2) = vm(comp(s2)) .
		
		eq eval(s2,eval(s1,empEnv)) = ev .
		
		-- check
		red th(s1 s2) .
	close