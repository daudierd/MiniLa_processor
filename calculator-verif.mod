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

-- BASE CASE
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
	red th1(v, e1 + e2) .
	red th1(v, sd(e1,e2)) .
	red th1(v, e1 * e2) .
	red th1(v, e1 / e2) .
	red th1(v, e1 % e2) .
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

-- THEOREM: INDUCTION CASE
open VERIFY-COMP .
	ops s1 s2 : -> Stm .
	-- lemma 1S
	eq exec(gen(S) @ IL, SE, EE) = exec(IL, SE, eval(S, EE)) .
	-- IH
	eq inter(s1) = vm(comp(s1)) .
	eq inter(s2) = vm(comp(s2)) .
	-- check
	red th(s1 s2) .
close