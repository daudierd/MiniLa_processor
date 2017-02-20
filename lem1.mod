in calculator.mod
in del.mod

-- -----------
-- LEMMA 1E --
-- -----------

-- exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EV) = exec(IL1 @ genExp(E) @ IL2, len(IL1) + len(genExp(E)), evalExp(E, EV) | SE, EV)

open VERIFY-COMP .
	op en : -> ExpPNat .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	-- lemma Pev
	eq evalExp(EN, EV) = en2n(EN) .
	-- lemma X
	eq nth(len(IL1), IL1 @ IL2) = nth(0, IL2) .
	-- check
	red lem1E(en, il1, il2, stk, ev) .
	red lem1E(en, il1, il2, stk, errEnv) .
close

open VERIFY-COMP .
	ops e1 e2 : -> Exp .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	-- IH
	eq exec(IL1 @ genExp(e1) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(e1) @ IL2, len(IL1) + len(genExp(e1)), evalExp(e1, EE) | SE, EE) .
	eq exec(IL1 @ genExp(e2) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(e2) @ IL2, len(IL1) + len(genExp(e2)), evalExp(e2, EE) | SE, EE) .
	
	-- lemma 0
		eq len(IL1) + len(IL2) = len(IL2 @ IL1) .
	-- lemma X
		eq nth(len(IL1), IL1 @ IL2) = nth(0, IL2) .
	-- lemma Y-2
		eq len(IL @ genExp(E1) @ genExp(E2) @ (I | iln)) = s(len(IL @ genExp(E1) @ genExp(E2))) .
	
	-- check
	red lem1E(e1 + e2, il1, il2, stk, ev) .
	red lem1E(e1 - e2, il1, il2, stk, ev) .
	red lem1E(e1 * e2, il1, il2, stk, ev) .
	red lem1E(e1 / e2, il1, il2, stk, ev) .
	red lem1E(e1 % e2, il1, il2, stk, ev) .
	-- Under hypothesis
		ops n1 n2 : -> PNat .
		eq evalExp(e1,ev) = n1 .
		eq evalExp(e2,ev) = n2 .
	red lem1E(e1 < e2, il1, il2, stk, ev) .
	red lem1E(e1 > e2, il1, il2, stk, ev) .
	red lem1E(e1 === e2, il1, il2, stk, ev) .
	red lem1E(e1 =!= e2, il1, il2, stk, ev) .
	red lem1E(e1 && e2, il1, il2, stk, ev) .
	red lem1E(e1 || e2, il1, il2, stk, ev) .
	
	--
	red lem1E(e1 + e2, il1, il2, stk, errEnv) .
	red lem1E(e1 - e2, il1, il2, stk, errEnv) .
	red lem1E(e1 * e2, il1, il2, stk, errEnv) .
	red lem1E(e1 / e2, il1, il2, stk, errEnv) .
	red lem1E(e1 % e2, il1, il2, stk, errEnv) .
	red lem1E(e1 < e2, il1, il2, stk, errEnv) .
	red lem1E(e1 > e2, il1, il2, stk, errEnv) .
	red lem1E(e1 === e2, il1, il2, stk, errEnv) .
	red lem1E(e1 =!= e2, il1, il2, stk, errEnv) .
	red lem1E(e1 && e2, il1, il2, stk, errEnv) .
	red lem1E(e1 || e2, il1, il2, stk, errEnv) .
	
close

-- -------------
-- LEMMA 1E-0 --
-- -------------

-- exec(genExp(E) @ IL, 0, SE, EV) = exec(genExp(E) @ IL, len(genExp(E)), evalExp(E, EV) | SE, EV)

open VERIFY-COMP .
	op e : -> Exp .
	op il : -> IList .
	op stk : -> Stack&Err .
	op ee : -> Env&Err .
	
	red lem1E(e, iln, il, stk, ee) implies lem1E-0(e, il, stk, ee) .
close

-- -----------
-- LEMMA 1S --
-- -----------

-- exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1) + len(gen(S)), SE, eval(S, EE))

-- LEMMA 1S: BASE CASE
	-- S = estm
open VERIFY-COMP .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	
	-- lem Iln
	eq IL @ iln = IL .
	-- check
	red lem1S(estm, il1, il2 , stk, ev) .
	red lem1S(estm, il1, il2 , stk, errEnv) .
close

	-- S = (V := E ;)
open VERIFY-COMP .
	op v : -> Var .
	ops e e1 e2 : -> Exp .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	
	-- lemma 0
		eq len(IL1) + len(IL2) = len(IL2 @ IL1) .
	-- lemma 1E
		eq exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(E) @ IL2, len(IL1) + len(genExp(E)), evalExp(E, EE) | SE, EE) .
	-- lemma X
		-- eq nth(len(IL1), IL1 @ IL2) = nth(0, IL2) .
	-- lemma Y-1
		-- eq len(IL @ genExp(E) @ (I | iln)) = s(len(IL @ genExp(E))) .
	
	-- check
	red lem1S(v := e ;, il1, il2, stk, ev) .
	red lem1S(v := e ;, il1, il2, stk, errEnv) .
close

	-- S = (if (E) { S1 } else { S2 })
	-- CASE 1
	open VERIFY-COMP .
		pr(DEL)
		op e : -> Exp .
		ops s1 s2 : -> Stm .
		ops il1 il2 : -> IList .
		op stk : -> Stack&Err .
		op ev : -> Env .
		
		-- Case splitting : evalExp(e, ev) = 0
			eq evalExp(e,ev) = 0 .
		
		-- lemma 0
			eq len(IL2 @ IL1) = len(IL1) + len(IL2) .
		-- lemma 1E
			eq exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(E) @ IL2, len(IL1) + len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- lemma 1S (Induction Hypothesis)
			eq exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
			
		-- Alternative version for lemma 1S
			eq exec2(hd(gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		-- lemma X
			eq nth(len(IL1), IL1 @ IL2) = nth(0, IL2) .
		-- lemma Y-1
			eq len(IL @ genExp(E) @ (I | iln)) = s(len(IL @ genExp(E))) .
		-- lemma nth
			eq nth(N, IL) = hd(del(N, IL)) .
		
		-- check
		-- red lem1S(if (e) { s1 } else { s2 }, il1, il2, stk, ev) .
		
			op pca : -> PNat .
			ops ila ilb : -> IList .
			
			eq pca = s(s(s((len(il1) + (len(gen(s1)) + len(genExp(e))))))) .
			eq ila = (il1 @ (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | (gen(s2) @ il2))))))) .
			
			eq ilb = il1 @ (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | iln))))) .
			
		-- phase 1 : LHS = f(X)
			red exec(il1 @ gen(if (e) { s1 } else { s2 }) @ il2, len(il1), stk, ev) = exec2(hd(gen(s2) @ il2),ila,pca,stk,ev) .
			
		-- phase 2 : X = Y
			red ila = ilb @ gen(s2) @ il2 .
			red len(ilb) = pca .
			
		-- phase 3 : f(Y) = RHS
			red exec2(hd(gen(s2) @ il2), ilb @ gen(s2) @ il2, len(ilb), stk, ev) = exec(il1 @ gen(if (e) { s1 } else { s2 }) @ il2, len(il1 @ gen(if (e) { s1 } else { s2 })), stk, eval(if (e) { s1 } else { s2 }, ev)) .
	close
	
	-- CASE 2.1
	open VERIFY-COMP .
	pr(DEL)
	op e : -> Exp .
	ops s1 s2 : -> Stm .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	ops ev ev2 : -> Env .
	
	-- Case splitting : evalExp(e, ev) > 0
		eq evalExp(e,ev) = s(N) .
		
	-- eval(s1,empEnv) is not errEnv
			eq eval(s1,ev) = ev2 .
	
	-- lemma 0
		eq len(IL2 @ IL1) = len(IL1) + len(IL2) .
	-- lemma 1E
		eq exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(E) @ IL2, len(IL1) + len(genExp(E)), evalExp(E, EE) | SE, EE) .
	-- lemma 1S (Induction Hypothesis)
		eq exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		
	-- Alternative version for lemma 1S
		eq exec2(hd(gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
	-- lemma X
		eq nth(len(IL1), IL1 @ IL2) = nth(0, IL2) .
	-- lemma Y-1
		eq len(IL @ genExp(E) @ (I | iln)) = s(len(IL @ genExp(E))) .
	-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
	
	-- check
	-- red lem1S(if (e) { s1 } else { s2 }, il1, il2, stk, ev) .
	
		op pca : -> PNat .
		ops ila il1b il2b : -> IList .
		
		eq pca = s(s((len(genExp(e)) + len(il1)))) .
		eq ila = (il1 @ (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | (gen(s2) @ il2))))))) .
		
		eq il1b = il1 @ (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | iln))) .
		
		eq il2b = (jump(s(len(gen(s2)))) | (gen(s2) @ il2)) .
		
	-- phase 1 : LHS = f(X)
		-- red lem1S(if (e) { s1 } else { s2 }, il1, il2, stk, ev) .
		red exec(il1 @ gen(if (e) { s1 } else { s2 }) @ il2, len(il1), stk, ev) = exec2(hd(gen(s1) @ il2b),ila,pca,stk,ev) .
		
	-- phase 2 : X = Y
		red ila = il1b @ gen(s1) @ il2b .
		red len(il1b) = pca .
		
	-- phase 3 : f(Y) = RHS
		red exec2(hd(gen(s1) @ il2b), il1b @ gen(s1) @ il2b, len(il1b), stk, ev) = exec(il1 @ gen(if (e) { s1 } else { s2 }) @ il2, len(il1 @ gen(if (e) { s1 } else { s2 })), stk, eval(if (e) { s1 } else { s2 }, ev)) .
	close

	-- CASE 2.2
	open VERIFY-COMP .
	pr(DEL)
	op e : -> Exp .
	ops s1 s2 : -> Stm .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	ops ev : -> Env .
	
	-- Case splitting : evalExp(e, ev) > 0
		eq evalExp(e,ev) = s(N) .
		
	-- eval(s1,empEnv) is not errEnv
			eq eval(s1,ev) = errEnv .
	
	-- lemma 0
		eq len(IL2 @ IL1) = len(IL1) + len(IL2) .
	-- lemma 1E
		eq exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(E) @ IL2, len(IL1) + len(genExp(E)), evalExp(E, EE) | SE, EE) .
	-- lemma 1S (Induction Hypothesis)
		eq exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		
	-- Alternative version for lemma 1S
		eq exec2(hd(gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
	-- lemma X
		eq nth(len(IL1), IL1 @ IL2) = nth(0, IL2) .
	-- lemma Y-1
		eq len(IL @ genExp(E) @ (I | iln)) = s(len(IL @ genExp(E))) .
	-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
	
	-- check
	-- red lem1S(if (e) { s1 } else { s2 }, il1, il2, s, ev) .
	
		op pca : -> PNat .
		ops ila il1b il2b : -> IList .
		
		eq pca = s(s((len(genExp(e)) + len(il1)))) .
		eq ila = (il1 @ (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | (gen(s2) @ il2))))))) .
		
		eq il1b = il1 @ (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | iln))) .
		
		eq il2b = (jump(s(len(gen(s2)))) | (gen(s2) @ il2)) .
		
	-- phase 1 : LHS = f(X)
		-- red lem1S(if (e) { s1 } else { s2 }, il1, il2, stk, ev) .
		red exec(il1 @ gen(if (e) { s1 } else { s2 }) @ il2, len(il1), stk, ev) = exec2(hd(gen(s1) @ il2b),ila,pca,stk,ev) .
		
	-- phase 2 : X = Y
		red ila = il1b @ gen(s1) @ il2b .
		red len(il1b) = pca .
		
	-- phase 3 : f(Y) = RHS
		red exec2(hd(gen(s1) @ il2b), il1b @ gen(s1) @ il2b, len(il1b), stk, ev) = exec(il1 @ gen(if (e) { s1 } else { s2 }) @ il2, len(il1 @ gen(if (e) { s1 } else { s2 })), stk, eval(if (e) { s1 } else { s2 }, ev)) .
	close

	
-- LEMMA 1S: INDUCTION CASE
open VERIFY-COMP .
	ops s1 s2 : -> Stm .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	
	-- lemma 0
	eq len(IL1) + len(IL2) = len(IL2 @ IL1) .
	-- IH
	eq exec(IL @ gen(s1) @ IL2, len(IL), SE, EE) = exec(IL @ gen(s1) @ IL2, len(IL) + len(gen(s1)), SE, eval(s1, EE)) .
	eq exec(IL @ gen(s2) @ IL2, len(IL), SE, EE) = exec(IL @ gen(s2) @ IL2, len(IL) + len(gen(s2)), SE, eval(s2, EE)) .
	-- check
	red lem1S((s1 s2), il1, il2, stk, ev) .
	red lem1S((s1 s2), il1, il2, stk, errEnv) .
close