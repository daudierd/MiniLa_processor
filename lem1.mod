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

-- INDUCTION CASE
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