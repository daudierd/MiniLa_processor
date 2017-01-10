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

-- -----------
-- LEMMA 1E --
-- -----------

-- exec(genExp(E) @ IL, SE, EE) = exec(IL, evalExp(E, EE) | SE, EE)

-- BASE CASE
	-- Exp -> PNat
open VERIFY-COMP .
	op en : -> ExpPNat .
	op il : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	-- lemma Pev
	eq evalExp(EN, EV) = en2n(EN) .
	-- check
	red lem1E(en, il, stk, errEnv) .
	red lem1E(en, il, stk, ev) .
close

	-- Exp -> Var
open VERIFY-COMP .
	op v : -> Var .
	op il : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	-- lemma Pev
	eq evalExp(EN, EV) = en2n(EN) .
	-- check
	red lem1E(v, il, stk, errEnv) .
	red lem1E(v, il, stk, ev) .
close

-- INDUCTION CASE
open VERIFY-COMP .
	ops e1 e2 : -> ExpPNat .
	op e : -> Exp .
	op il : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	-- lemma Pev
	eq evalExp(EN, EV) = en2n(EN) .
	-- IH
	eq exec(genExp(e1) @ IL, SE, EE) = exec(IL, evalExp(e1, EE) | SE, EE) .
	eq exec(genExp(e2) @ IL, SE, EE) = exec(IL, evalExp(e2, EE) | SE, EE) .
	-- check
	red lem1E(e,il,stk,errEnv) .
	
	red lem1E(e1 + e2,il,stk,ev) .
	red lem1E(sd(e1,e2),il,stk,ev) .
	red lem1E(e1 * e2,il,stk,ev) .
	red lem1E(e1 / e2,il,stk,ev) .
	red lem1E(e1 % e2,il,stk,ev) .
close

-- -----------
-- LEMMA 1S --
-- -----------

-- exec(gen(S) @ IL, SE, EE) = exec(IL, SE, eval(S, EE))

-- BASE CASE
	-- S = estm
open VERIFY-COMP .
	op il : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	-- check
	red lem1S(estm, il, stk, errEnv) .
	red lem1S(estm, il, stk, ev) .
close

	-- S = (V := E ;)
open VERIFY-COMP .
	op v : -> Var .
	op e : -> Exp .
	op il : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	-- lemma 1E
	eq exec(genExp(E) @ IL, SE, EV) = exec(IL, evalExp(E, EV) | SE, EV) .
	-- check
	red lem1S(v := e ;, il, stk, errEnv) .
	red lem1S(v := e ;, il, stk, ev) .
close

-- INDUCTION CASE
open VERIFY-COMP .
	ops s1 s2 : -> Stm .
	op il : -> IList .
	op stk : -> Stack&Err .
	op ev : -> Env .
	-- IH
	eq exec(gen(s1) @ IL, SE, EE) = exec(IL, SE, eval(s1, EE)) .
	eq exec(gen(s2) @ IL, SE, EE) = exec(IL, SE, eval(s2, EE)) .
	-- check
	red lem1S((s1 s2), il, stk, errEnv) .
	red lem1S((s1 s2), il, stk, ev) .
close