-- ----------------------------------------------------------
--                                                         --
--       MiniLa language processor verified compiler       --
--                      PROOF  SCORES                      --
--                                                         --
--                     DAUDIER, Dorian                     --
--            Special research student at JAIST            --
--                                                         --
-- ----------------------------------------------------------

in calculator.mod
in del.mod

-- --------------------------------------------
-- NTH-DEL PROOF CAN BE FOUND IN nth-del.mod --
-- --------------------------------------------

-- nth(N, IL) = hd(del(N, IL))


-- -------------
-- LEMMA Ladd --
-- -------------

open VERIFY-COMP .
	op il : -> IList .
	-- check
	red lemLadd(iln, il) .
close

open VERIFY-COMP .
	ops il1 il2 : -> IList .
	op i : -> Instr .
	-- IH
	eq len(il1) + len(il2) = len(il1 @ il2) .
	-- check
	red lemLadd(i | il1, il2) .
close

-- ------------
-- LEMMA Pev --
-- ------------

open VERIFY-COMP .
	op ev : -> Env .
	-- check
	red lemPev(0, ev) .
close

open VERIFY-COMP .
	op en : -> ExpPNat .
	op ev : -> Env .
	-- IH
	eq evalExp(en, EV) = en2n(en) .
	-- check
	red lemPev(s(en), ev) .
close

-- ------------------------------------------
-- LEMMA 1 PROOFS CAN BE FOUND IN lem1.mod --
-- ------------------------------------------

-- exec(genExp(E) @ IL, Stk, EV) = exec(IL, evalExp(E, EV) | Stk, EV)
-- exec(gen(S) @ IL, SE, EE) = exec(IL, SE, eval(S, EE))

-- ---------------
--    THEOREM   --
-- SUB-CASE TH1 --
-- ---------------

-- inter(V := E ;) = vm(comp(V := E ;))

-- Exp -> PNat
open VERIFY-COMP .
	op en : -> ExpPNat .
	op v : -> Var .
	-- lemma Pev
	eq evalExp(EN, EV) = en2n(EN) .
	-- check
	red th1(v, en) .
close

-- Exp -> Var
open VERIFY-COMP .
	ops v x : -> Var .
	-- check
	red th1(v, x) .
close

-- Exp -> any expression
	-- Case splitting: update(empEnv,v,evalExp(e,empEnv)) = errEnv
	open VERIFY-COMP .
		pr(DEL)
		op e : -> Exp .
		op v : -> Var .
		-- lemma 1E
		eq exec(genExp(E) @ IL, 0, SE, EE) = exec(genExp(E) @ IL, len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		-- case splitting hypothesis
		eq update(empEnv,v,evalExp(e,empEnv)) = errEnv .
		-- check
		red th1(v, e) .
	close
	
	-- Case splitting: update(empEnv,v,evalExp(e,empEnv)) <> errEnv
	open VERIFY-COMP .
		pr(DEL)
		op e : -> Exp .
		op v : -> Var .
		op ev : -> Env .
		-- lemma 1E-0
		eq exec(genExp(E) @ IL2, 0, SE, EE) = exec(genExp(E) @ IL2, len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		-- case splitting hypothesis
		eq update(empEnv,v,evalExp(e,empEnv)) = ev .
		-- check
		red th1(v, e) .
	close

-- ----------
-- THEOREM --
-- ----------

-- inter(S) = vm(comp(S))

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
	-- theorem th1 being a special case of the main theorem
	red th1(v,e) implies th(v := e ;) . 
close

-- Stm = if E { S1 } else { S2 }
	-- CASE 1 : Case splitting, evalExp(e, empEnv) = 0
	open VERIFY-COMP .
		pr(DEL)
		op e : -> Exp .
		ops s1 s2 : -> Stm .
		ops il1 il2 : -> IList .
		
	-- HYPOTHESIS
		-- Case splitting : evalExp(e, empEnv) = 0
		eq evalExp(e,empEnv) = 0 .
		
	-- LEMMAS
		-- lemma Ladd (reversed)
		eq len(IL1 @ IL2) = len(IL1) + len(IL2) .
		-- lemma 1E-0
		eq exec(genExp(E) @ IL2, 0, SE, EE) = exec(genExp(E) @ IL2, len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		-- lemma 1S (version with exec2)
		eq exec2(nth(0,gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec2(nth(0,IL2), IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		
	-- CHECK: 3-stepped verification
		-- We use a 3-stepped verification combined with strategy chosen for exec2, to avoid parenthesis reorganization and use lemma 1S
			op pca : -> PNat .
			ops ila il1b il2b : -> IList .
			
			eq pca = s(s(s((len(gen(s1)) + len(genExp(e)))))) .
			eq ila = (genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | (gen(s2) @ (quit | iln))))))) .
			
			eq il1b = genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | iln)))) .
			eq il2b = (quit | iln) .
		-- step 1 : LHS = f(X)
		red vm(comp(if e {s1} else {s2})) = exec2(nth(0, gen(s2) @ il2b), ila, pca, empstk, empEnv) .
		
		-- step 2 : X = Y
		red ila = il1b @ gen(s2) @ il2b .
		red len(il1b) = pca .
		
		-- step 3 : f(Y) = RHS
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
		
	-- HYPOTHESIS
		-- Case splitting : evalExp(e, ev) > 0
		eq evalExp(e,empEnv) = s(N) .
		-- eval(s1,empEnv) is not errEnv
		eq eval(s1,empEnv) = ev .
		
	-- LEMMAS
		-- lemma Ladd (reversed)
		eq len(IL1 @ IL2) = len(IL1) + len(IL2) .
		-- lemma 1E-0
		eq exec(genExp(E) @ IL2, 0, SE, EE) = exec(genExp(E) @ IL2, len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		-- lemma 1S (version with exec2)
		eq exec2(nth(0,gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec2(nth(0,IL2), IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
			
		-- CHECK: 3-stepped verification
				op pca : -> PNat .
				ops ila il1b il2b : -> IList .
				
				eq pca = s(s(len(genExp(e)))) .
				eq ila = genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | (gen(s2) @ (quit | iln)))))) .
				
				eq il1b = genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | iln)) .
				eq il2b = (jump(s(len(gen(s2)))) | (gen(s2) @ (quit | iln))) .
			
			-- step 1 : LHS = f(X)
			red vm(comp(if e {s1} else {s2})) = exec2(nth(0, gen(s1) @ il2b), ila, pca, empstk, empEnv) .
			
			-- step 2 : X = Y
			red ila = il1b @ gen(s1) @ il2b .
			red len(il1b) = pca .
			
			-- step 3 : f(Y) = RHS
			red exec2(nth(0, gen(s1) @ il2b), il1b @ gen(s1) @ il2b, len(il1b), empstk, empEnv) = inter(if e {s1} else {s2}) .
	close
	
	-- CASE 2.2 : Case splitting, evalExp(e, empEnv) > 0
	-- eval(s1,empEnv) has error
	open VERIFY-COMP .
		pr(DEL)
		op e : -> Exp .
		ops s1 s2 : -> Stm .
		ops il1 il2 : -> IList .
		
	-- HYPOTHESIS
		-- Case splitting : evalExp(e, empEnv) > 0
		eq evalExp(e,empEnv) = s(N) .
		-- eval(s1,empEnv) is errEnv
		eq eval(s1,empEnv) = errEnv .
	
	-- LEMMAS
		-- lemma Ladd (reversed)
		eq len(IL1 @ IL2) = len(IL1) + len(IL2) .
		-- lemma 1E-0
		eq exec(genExp(E) @ IL2, 0, SE, EE) = exec(genExp(E) @ IL2, len(genExp(E)), evalExp(E, EE) | SE, EE) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		-- lemma 1S (version with exec2)
		eq exec2(nth(0,gen(S) @ IL2), IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec2(nth(0,IL2), IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
			
		-- CHECK: 3-stepped verification
				op pca : -> PNat .
				ops ila il1b il2b : -> IList .
				
				eq pca = s(s(len(genExp(e)))) .
				eq ila = genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | (gen(s1) @ (jump(s(len(gen(s2)))) | (gen(s2) @ (quit | iln)))))) .
				
				eq il1b = genExp(e) @ (jumpOnCond(s(s(0))) | (jump(s(s(len(gen(s1))))) | iln)) .
				eq il2b = (jump(s(len(gen(s2)))) | (gen(s2) @ (quit | iln))) .
			
			red vm(comp(if e {s1} else {s2})) .
			
			-- step 1 : LHS = f(X)
			red vm(comp(if e {s1} else {s2})) = exec2(nth(0, gen(s1) @ il2b), ila, pca, empstk, empEnv) .
			
			-- step 2 : X = Y
			red ila = il1b @ gen(s1) @ il2b .
			red len(il1b) = pca .
			
			-- step 3 : f(Y) = RHS
			red exec2(nth(0, gen(s1) @ il2b), il1b @ gen(s1) @ il2b, len(il1b), empstk, empEnv) = inter(if e {s1} else {s2}) .
	close

-- THEOREM: INDUCTION CASE
	-- case splitting: eval(s2,eval(s1,empEnv)) = ErrEnv
	open VERIFY-COMP .
		pr(DEL)
		ops s1 s2 : -> Stm .
		
		-- lemma 1S
		eq exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		eq exec(gen(S) @ IL2, 0, SE, EE) = exec(gen(S) @ IL2, len(gen(S)), SE, eval(S, EE)) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		-- IH
		eq inter(s1) = vm(comp(s1)) .
		eq inter(s2) = vm(comp(s2)) .
		-- case splitting hypothesis
		eq eval(s2,eval(s1,empEnv)) = errEnv .
		
		-- check
		red th(s1 s2) .
	close
	
	-- case splitting: eval(s2,eval(s1,empEnv)) <> ErrEnv
	open VERIFY-COMP .
		pr(DEL)
		ops s1 s2 : -> Stm .
		op ev : -> Env .
		-- lemma 1S
		eq exec(IL1 @ gen(S) @ IL2, len(IL1), SE, EE) = exec(IL1 @ gen(S) @ IL2, len(IL1 @ gen(S)), SE, eval(S, EE)) .
		-- lemma 1S-0
		eq exec(gen(S) @ IL2, 0, SE, EE) = exec(gen(S) @ IL2, len(gen(S)), SE, eval(S, EE)) .
		-- Nth-del theorem
		eq nth(N, IL) = hd(del(N, IL)) .
		-- IH
		eq inter(s1) = vm(comp(s1)) .
		eq inter(s2) = vm(comp(s2)) .
		-- case splitting hypothesis
		eq eval(s2,eval(s1,empEnv)) = ev .
		
		-- check
		red th(s1 s2) .
	close