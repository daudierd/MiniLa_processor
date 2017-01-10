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

-- ----------
-- LEMMA 1 --
-- ----------

-- exec(genExp(E) @ IL, Stk, EV) = exec(IL, evalExp(E, EV) | Stk, EV) .

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
	red lem1(en, il, stk, errEnv) .
	red lem1(en, il, stk, ev) .
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
	red lem1(v, il, stk, errEnv) .
	red lem1(v, il, stk, ev) .
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
	red lem1(e,il,stk,errEnv) .
	
	red lem1(e1 + e2,il,stk,ev) .
	red lem1(sd(e1,e2),il,stk,ev) .
	red lem1(e1 * e2,il,stk,ev) .
	red lem1(e1 / e2,il,stk,ev) .
	red lem1(e1 % e2,il,stk,ev) .
close

-- ----------
-- THEOREM --
-- ----------

-- BASE CASE
	-- Exp -> PNat
open VERIFY-COMP .
	op en : -> ExpPNat .
	op v : -> Var .
	-- lemma Pev
	eq evalExp(EN, EV) = en2n(EN) .
	-- check
	red th(v, en) .
close

	-- Exp -> Var
open VERIFY-COMP .
	ops v x : -> Var .
	-- check
	red th(v, x) .
close

-- INDUCTION CASE
open VERIFY-COMP .
	ops e1 e2 : -> Exp .
	op v : -> Var .
	-- lemma Pev
	eq evalExp(EN, EV) = en2n(EN) .
	-- lemma 1
	eq exec(genExp(E) @ IL, SE, EE) = exec(IL, evalExp(E, EE) | SE, EE) .
	-- IH
	eq inter(V := e1 ;) = vm(comp(V := e1 ;)) .
	eq inter(V := e2 ;) = vm(comp(V := e2 ;)) .
	-- check
	red th(v, e1 + e2) .
	red th(v, sd(e1,e2)) .
	red th(v, e1 * e2) .
	red th(v, e1 / e2) .
	red th(v, e1 % e2) .
close