in calculator.mod

-- ----------
-- LEMMA 1 --
-- ----------

open VERIFY-COMP .
	op ev : -> Env .
	-- check
	red lemPev(0, ev) .
close

open VERIFY-COMP .
	op en : -> ExpPNat .
	op ev : -> Env .
	-- IH
	eq inter(en, EV) = en2n(en) .
	-- check
	red lemPev(s(en), ev) .
close

-- ----------
-- LEMMA 2 --
-- ----------

-- LEMMA 2: BASE CASE
	-- Exp -> PNat
open VERIFY-COMP .
	op en : -> ExpPNat .
	op il : -> IList .
	op s : -> Stack .
	op ev : -> Env .
	-- check
	red lem1(en, il, s, ev) .
close

	-- Exp -> Var
open VERIFY-COMP .
	op v : -> Var .
	op il : -> IList .
	op s : -> Stack .
	op ev : -> Env .
	-- check
	red lem1(v, il, s, ev) .
close

-- LEMMA 2: INDUCTION CASE
open VERIFY-COMP .
	ops e1 e2 : -> ExpPNat .
	op il : -> IList .
	op s : -> Stack .
	op ev : -> Env .
	-- IH
	eq exec(comp(e1) @ IL, Stk, EV) = exec(IL, vm(comp(e1), EV) | Stk, EV) .
	eq exec(comp(e2) @ IL, Stk, EV) = exec(IL, vm(comp(e2), EV) | Stk, EV) .
	-- check
	red lem1(e1 + e2,il,s,ev) .
	red lem1(e1 - e2,il,s,ev) .
	red lem1(e1 * e2,il,s,ev) .
	red lem1(e1 / e2,il,s,ev) .
	red lem1(e1 % e2,il,s,ev) .
close

-- ----------
-- THEOREM --
-- ----------

-- THEOREM: BASE CASE
	-- Exp -> PNat
open VERIFY-COMP .
	op en : -> ExpPNat .
	op ev : -> Env .
	-- lemma 1
	eq inter(EN, EV) = en2n(EN) .
	-- check
	red th(en, ev) .
close

	-- Exp -> Var
open VERIFY-COMP .
	op v : -> Var .
	op ev : -> Env .
	-- lemma 1
	eq inter(EN, EV) = en2n(EN) .
	-- check
	red th(v, ev) .
close

-- THEOREM: INDUCTION CASE
open VERIFY-COMP .
	ops e1 e2 : -> Exp .
	op ev : -> Env .
	-- lemma 1
	eq inter(EN, EV) = en2n(EN) .
	-- lemma 2
	eq exec(comp(E) @ IL, Stk, EV) = exec(IL, vm(comp(E), EV) | Stk, EV) .
	-- IH
	eq inter(e1, EV) = vm(comp(e1), EV) .
	eq inter(e2, EV) = vm(comp(e2), EV) .
	-- check
	red th(e1 + e2, ev) .
	red th(e1 - e2, ev) .
	red th(e1 * e2, ev) .
	red th(e1 / e2, ev) .
	red th(e1 % e2, ev) .
close