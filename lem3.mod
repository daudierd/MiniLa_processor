in calculator.mod
in eval.mod
in del.mod

-- ----------
-- LEMMA 3 --
-- ----------

-- tc(e, s, ev, n) implies eval(while e {s}, ev) = eval(n, s, ev) .

-- BASE CASE
open VERIFY-COMP .
	pr(EVAL)
	pr(DEL)
	op e : -> Exp .
	op s : -> Stm .
	op ev : -> Env .
	
	-- Termination Hypothesis
	eq evalExp(e,ev) = 0 .
	
	-- check
	red eval(while e {s}, ev) = eval(0, s, ev) .
close

-- INDUCTION CASE
open VERIFY-COMP .
	pr(EVAL)
	pr(DEL)
	ops n m k : -> PNat .
	op e : -> Exp .
	op s : -> Stm .
	op ev : -> Env .
	
	-- Termination hypothesis tc(e, s, ev, s(n))
	ceq evalExp(e,eval(K, s, ev)) = s(0) if (K < s(n)) .
	eq evalExp(e,eval(s(n), s, ev)) = 0 .
	
	-- Induction Hypothesis
		-- check predicate tc(e, s, eval(s,ev), n)
		eq (k < n) = true .
		red evalExp(e,eval(k, s, eval(s,ev))) = s(0) .
		red evalExp(e,eval(n, s, eval(s,ev))) = 0 .
		-- equation
		eq eval(while e {s}, eval(s,ev)) = eval(n, s, eval(s,ev)) .
	
	-- rewriting evalExp(e,ev)
		red evalExp(e,ev) = evalExp(e,eval(0, s, ev)) .
		red 0 < s(n) .
		-- provided two previous scores are true:
		eq evalExp(e,ev) = s(0) .
	
	-- check
	red eval(while e {s}, ev) = eval(s(n), s, ev) .
close