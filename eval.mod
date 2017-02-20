in calculator.mod

mod! EVAL {
	pr(COMP)
	pr(VM)
	pr(INTER)
	
	op eval : PNat&Err Stm&Err Env&Err -> Env&Err {strat (0 1 0)} .
	
	vars K N : PNat . var S : Stm . var EE : Env&Err . var EV : Env .
	eq eval(errPNat, S, EE) = errEnv .
	eq eval(N, errStm, EE) = errEnv .
	eq eval(0, S, EE) = EE .
	-- eq eval(s(N), S, EE) = eval(S, eval(N, S, EE)) .
	eq eval(S, eval(N, S, EE)) = eval(s(N), S, EE) .
	
	-- to prove
	eq eval(N, S, eval(S, EE)) = eval(s(N), S, EE) .
}
