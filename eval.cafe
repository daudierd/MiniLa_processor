-- ----------------------------------------------------------
--                                                         --
--       MiniLa language processor verified compiler       --
--          PRACTICAL DEFINITION OF EVAL OPERATOR          --
--                                                         --
--                     DAUDIER, Dorian                     --
--            Special research student at JAIST            --
--                                                         --
-- ----------------------------------------------------------

-- in calculator.mod

mod! EVAL {
	pr(COMP)
	pr(VM)
	pr(INTER)
	
	op eval : PNat&Err Stm Env&Err -> Env&Err {strat (0 1 0)} .
	
	-- definition
	var N : PNat . var S : Stm . var EE : Env&Err . var EV : Env .
	eq eval(errPNat, S, EV) = errEnv .
	eq eval(N, S, errEnv) = errEnv .
	eq eval(0, S, EV) = EV .
	eq eval(S, eval(N, S, EE)) = eval(s(N), S, EE) . -- reversed for rewriting purposes
	
	-- equation proved
	eq eval(N, S, eval(S, EE)) = eval(S, eval(N, S, EE)) .
}
