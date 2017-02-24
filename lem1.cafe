-- ----------------------------------------------------------
--                                                         --
--       MiniLa language processor verified compiler       --
--                 PROOF  SCORES - LEMMA 1                 --
--                                                         --
--                     DAUDIER, Dorian                     --
--            Special research student at JAIST            --
--                                                         --
-- ----------------------------------------------------------

in calculator.mod
in del.mod

-- ------------------------------------------
-- LEMMA Y PROOFS CAN BE FOUND IN lemY.mod --
-- ------------------------------------------

-- len(IL @ (I | iln)) = s(len(IL))
-- len(IL @ genExp(E) @ (I | iln)) = s(len(IL @ genExp(E)))
-- len(IL @ genExp(E1) @ genExp(E2) @ (I | iln)) = s(len(IL @ genExp(E1) @ genExp(E2)))

	-- nb: lemma X is no longer needed
	
-- --------------------------------------------
-- NTH-DEL PROOF CAN BE FOUND IN nth-del.mod --
-- --------------------------------------------

-- nth(N, IL) = hd(del(N, IL))


-- -----------
-- LEMMA 1E --
-- -----------

-- exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(E) @ IL2, len(genExp(E)) + len(IL1), evalExp(E, EE) | SE, EE)

-- BASE CASE
	-- Exp -> PNat
open VERIFY-COMP .
	pr(DEL)
	op en : -> ExpPNat .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	
	-- lemma Pev
	eq evalExp(EN, EV) = en2n(EN) .
	-- Nth-del theorem
	eq nth(N, IL) = hd(del(N, IL)) .
	-- check
	red lem1E(en, il1, il2, stk, errEnv) .
	red lem1E(en, il1, il2, stk, ev) .
close

	-- Exp -> Var
open VERIFY-COMP .
	pr(DEL)
	op v : -> Var .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	
	-- lemma Pev
	eq evalExp(EN, EV) = en2n(EN) .
	-- Nth-del theorem
	eq nth(N, IL) = hd(del(N, IL)) .
	-- check
	red lem1E(v, il1, il2, stk, errEnv) .
	red lem1E(v, il1, il2, stk, ev) .
close

-- INDUCTION CASE
open VERIFY-COMP .
	pr(DEL)
	ops e e1 e2 : -> Exp .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	
	-- IH
	eq exec(IL1 @ genExp(e1) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(e1) @ IL2, len(genExp(e1)) + len(IL1), evalExp(e1, EE) | SE, EE) .
	eq exec(IL1 @ genExp(e2) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(e2) @ IL2, len(genExp(e2)) + len(IL1), evalExp(e2, EE) | SE, EE) .
	
	-- lemma Ladd
	eq len(IL1) + len(IL2) = len(IL1 @ IL2) .
	-- Nth-del theorem
	eq nth(N, IL) = hd(del(N, IL)) .
	-- lemma Y-2
	eq len(IL @ genExp(E1) @ genExp(E2) @ (I | iln)) = s(len(IL @ genExp(E1) @ genExp(E2))) .
	
	-- check
	red lem1E(e, il1, il2, stk, errEnv) .
	red lem1E(e1 + e2, il1, il2, stk, ev) .
	red lem1E(sd(e1,e2), il1, il2, stk, ev) .
	red lem1E(e1 * e2, il1, il2, stk, ev) .
	red lem1E(e1 / e2, il1, il2, stk, ev) .
	red lem1E(e1 % e2, il1, il2, stk, ev) .
	
	-- Boolean operations
		-- e1 and e2 evaluate as natural numbers
		ops n1 n2 : -> PNat .
		eq evalExp(e1,ev) = n1 .
		eq evalExp(e2,ev) = n2 .
	red lem1E(e1 < e2, il1, il2, stk, ev) .
	red lem1E(e1 > e2, il1, il2, stk, ev) .
	red lem1E(e1 === e2, il1, il2, stk, ev) .
	red lem1E(e1 =!= e2, il1, il2, stk, ev) .
	red lem1E(e1 && e2, il1, il2, stk, ev) .
	red lem1E(e1 || e2, il1, il2, stk, ev) .
close

-- -----------
-- LEMMA 1S --
-- -----------

-- exec(gen(S) @ IL, SE, EE) = exec(IL, SE, eval(S, EE))

-- BASE CASE
	-- S = estm
open VERIFY-COMP .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	-- check
	red lem1S(estm, il1, il2, stk, errEnv) .
	red lem1S(estm, il1, il2, stk, ev) .
close

	-- S = (V := E ;)
open VERIFY-COMP .
	pr(DEL)
	op v : -> Var .
	op e : -> Exp .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	
	-- lemma Ladd
	eq len(IL1) + len(IL2) = len(IL1 @ IL2) .
	-- Nth-del theorem
	eq nth(N, IL) = hd(del(N, IL)) .
	-- lemma Y-1
	eq len(IL @ genExp(E) @ (I | iln)) = s(len(IL @ genExp(E))) .
	-- lemma 1E
	eq exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(E) @ IL2, len(genExp(E)) + len(IL1), evalExp(E, EE) | SE, EE) .
	
	-- check
	red lem1S(v := e ;, il1, il2, stk, errEnv) .
	red lem1S(v := e ;, il1, il2, stk, ev) .
close

-- PRELIMINARY: Lemma 1S with exec2 & hd
-- exec2(hd(gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EV = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EV))
open VERIFY-COMP .
	pr(DEL)
	op s : -> Stm .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	
	-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		
	-- CHECK
		-- PART 1
		red exec2(nth(0, gen(s) @ il2), il1 @ gen(s) @ il2, len(il1), stk, ev) = exec(il1 @ gen(s) @ il2, len(il1), stk, ev) .
		
		-- lemma 1S
		eq exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .

		-- PART 2
		red exec2(hd(gen(s) @ il2), il1 @ gen(s) @ il2, len(il1), stk, ev) = exec2(nth(0, gen(s) @ il2), il1 @ gen(s) @ il2, len(il1), stk, ev) .
		red exec(il1 @ gen(s) @ il2, len(il1), stk, ev) = exec(il1 @ gen(s) @ il2, len(il1 @ gen(s)), stk, eval(s, ev)) .
close

-- INDUCTION BY CONDITIONAL STRUCTURE
	-- CASE 1 : Case splitting, evalExp(e, ev) = 0
	open VERIFY-COMP .
		pr(DEL)
		op e : -> Exp .
		ops s1 s2 : -> Stm .
		ops il1 il2 : -> IList .
		op stk : -> Stack&Err .
		op ev : -> Env .
		
	-- HYPOTHESIS
		-- Case splitting : evalExp(e, ev) = 0
		eq evalExp(e,ev) = 0 .
		-- lemma 1S (Induction Hypothesis)
		eq exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		-- lemma 1S (Induction Hypothesis, with exec2 & hd)
		eq exec2(hd(gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		
	-- LEMMAS
		-- lemma Ladd (reversed)
		eq len(IL2 @ IL1) = len(IL1) + len(IL2) .
		-- lemma 1E
		eq exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(E) @ IL2, len(IL1) + len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		-- lemma Y-1
		eq len(IL @ genExp(E) @ (I | iln)) = s(len(IL @ genExp(E))) .
		
		-- CHECK: 3-stepped verification
			-- We use a 3-stepped verification combined with strategy chosen for exec2, to avoid parenthesis reorganization and use lemma 1S
			op pca : -> PNat .
			ops ila ilb : -> IList .
			
			eq pca = s(s(s((len(il1) + (len(gen(s1)) + len(genExp(e))))))) .
			eq ila = (il1 @ (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | (gen(s2) @ il2))))))) .
			
			eq ilb = il1 @ (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | iln))))) .
			
		-- step 1 : LHS = f(X)
			red exec(il1 @ gen(if (e) { s1 } else { s2 }) @ il2, len(il1), stk, ev) = exec2(hd(gen(s2) @ il2),ila,pca,stk,ev) .
			
		-- step 2 : X = Y
			red ila = ilb @ gen(s2) @ il2 .
			red len(ilb) = pca .
			
		-- step 3 : f(Y) = RHS
			red exec2(hd(gen(s2) @ il2), ilb @ gen(s2) @ il2, len(ilb), stk, ev) = exec(il1 @ gen(if (e) { s1 } else { s2 }) @ il2, len(il1 @ gen(if (e) { s1 } else { s2 })), stk, eval(if (e) { s1 } else { s2 }, ev)) .
	close
	
	-- CASE 2.1 : Case splitting, evalExp(e, ev) > 0
	-- eval(s1,empEnv) has no error
	open VERIFY-COMP .
		pr(DEL)
		op e : -> Exp .
		ops s1 s2 : -> Stm .
		ops il1 il2 : -> IList .
		op stk : -> Stack&Err .
		ops ev ev2 : -> Env .
	-- HYPOTHESIS
		-- Case splitting : evalExp(e, ev) > 0
		eq evalExp(e,ev) = s(N) .
		-- eval(s1,ev) is not errEnv
		eq eval(s1,ev) = ev2 .
		-- lemma 1S (Induction Hypothesis)
		eq exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		-- lemma 1S (Induction Hypothesis, with exec2 & hd)
		eq exec2(hd(gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		
	-- LEMMAS
		-- lemma Ladd (reversed)
		eq len(IL2 @ IL1) = len(IL1) + len(IL2) .
		-- lemma 1E
		eq exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(E) @ IL2, len(IL1) + len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		-- lemma Y-1
		eq len(IL @ genExp(E) @ (I | iln)) = s(len(IL @ genExp(E))) .

	-- CHECK: 3-stepped verification
			op pca : -> PNat .
			ops ila il1b il2b : -> IList .
			
			eq pca = s(s((len(genExp(e)) + len(il1)))) .
			eq ila = (il1 @ (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | (gen(s2) @ il2))))))) .
			
			eq il1b = il1 @ (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | iln))) .
			eq il2b = (jump(s(len(gen(s2)))) | (gen(s2) @ il2)) .
		
	-- step 1 : LHS = f(X)
		red exec(il1 @ gen(if (e) { s1 } else { s2 }) @ il2, len(il1), stk, ev) = exec2(hd(gen(s1) @ il2b),ila,pca,stk,ev) .
		
	-- step 2 : X = Y
		red ila = il1b @ gen(s1) @ il2b .
		red len(il1b) = pca .
		
	-- step 3 : f(Y) = RHS
		red exec2(hd(gen(s1) @ il2b), il1b @ gen(s1) @ il2b, len(il1b), stk, ev) = exec(il1 @ gen(if (e) { s1 } else { s2 }) @ il2, len(il1 @ gen(if (e) { s1 } else { s2 })), stk, eval(if (e) { s1 } else { s2 }, ev)) .
	close
	
	-- CASE 2.2 : Case splitting, evalExp(e, ev) > 0
	-- eval(s1,ev) has error
	open VERIFY-COMP .
	pr(DEL)
	op e : -> Exp .
	ops s1 s2 : -> Stm .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	ops ev : -> Env .

	-- HYPOTHESIS
		-- Case splitting : evalExp(e, ev) > 0
		eq evalExp(e,ev) = s(N) .
		-- eval(s1,ev) is errEnv
		eq eval(s1,ev) = errEnv .
		-- lemma 1S (Induction Hypothesis)
		eq exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		-- lemma 1S (Induction Hypothesis, with exec2 & hd)
		eq exec2(hd(gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .

	-- LEMMAS
		-- lemma Ladd (reversed)
		eq len(IL2 @ IL1) = len(IL1) + len(IL2) .
		-- lemma 1E
		eq exec(IL1 @ genExp(E) @ IL2, len(IL1), SE, EE) = exec(IL1 @ genExp(E) @ IL2, len(IL1) + len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		-- lemma Y-1
		eq len(IL @ genExp(E) @ (I | iln)) = s(len(IL @ genExp(E))) .

	-- CHECK: 3-stepped verification
			op pca : -> PNat .
			ops ila il1b il2b : -> IList .
			
			eq pca = s(s((len(genExp(e)) + len(il1)))) .
			eq ila = (il1 @ (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | (gen(s2) @ il2))))))) .
			
			eq il1b = il1 @ (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | iln))) .
			eq il2b = (jump(s(len(gen(s2)))) | (gen(s2) @ il2)) .
		
	-- step 1 : LHS = f(X)
		red exec(il1 @ gen(if (e) { s1 } else { s2 }) @ il2, len(il1), stk, ev) = exec2(hd(gen(s1) @ il2b),ila,pca,stk,ev) .
		
	-- step 2 : X = Y
		red ila = il1b @ gen(s1) @ il2b .
		red len(il1b) = pca .
		
	-- step 3 : f(Y) = RHS
		red exec2(hd(gen(s1) @ il2b), il1b @ gen(s1) @ il2b, len(il1b), stk, ev) = exec(il1 @ gen(if (e) { s1 } else { s2 }) @ il2, len(il1 @ gen(if (e) { s1 } else { s2 })), stk, eval(if (e) { s1 } else { s2 }, ev)) .
	close

-- INDUCTION BY SEQUENTIAL COMPOSITION
open VERIFY-COMP .
	ops s1 s2 : -> Stm .
	ops il1 il2 : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	-- lemma Ladd
	eq len(IL1) + len(IL2) = len(IL1 @ IL2) .
	-- IH
	eq exec(IL @ gen(s1) @ IL2, len(IL), SE, EE) = exec(IL @ gen(s1) @ IL2, len(gen(s1)) + len(IL), SE, eval(s1, EE)) .
	eq exec(IL @ gen(s2) @ IL2, len(IL), SE, EE) = exec(IL @ gen(s2) @ IL2, len(gen(s2)) + len(IL), SE, eval(s2, EE)) .
	-- check
	red lem1S((s1 s2), il1, il2, stk, errEnv) .
	red lem1S((s1 s2), il1, il2, stk, ev) .
close