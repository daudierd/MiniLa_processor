in calculator.mod

mod! NTHPAIR {
	pr(PAIR(PNAT, ILIST) * { sort Pair -> NthPair })
	op s : NthPair -> NthPair .
	op 1st : NthPair -> PNat .
	op 2nd : NthPair -> IList .
	
	var N : PNat . var IL : IList .
	eq s(N,IL) = (s(N), IL) .
	eq 1st(N,IL) = N .
	eq 2nd(N,IL) = IL .
}

mod! SIMPLIFY { pr(PNAT) pr(ILIST) pr(NTHPAIR) pr(VM)
	op simplify : NthPair -> NthPair {strat (0 1 0)} .	-- this strategy is necessary to reduce the 2nd case following module definition
	op s-th : PNat IList -> Bool .
	
	vars IL IL1 IL2 : IList . vars N M : PNat . var I : Instr .
	-- simplification already handled by nth operator
	eq simplify(s(N), I | IL) = simplify(N, IL) .
	
	-- new simplification equations
	eq simplify(len(IL1), IL1 @ IL2) = (0, IL2) .
	eq simplify(len(IL1) + N, IL1 @ IL2) = simplify(N, IL2) .
	eq simplify(s(M), IL1 @ IL2) = simplify(s(simplify(M, IL1 @ IL2))) .
	eq simplify(s(M) + N, IL1 @ IL2) = simplify(s(simplify(M + N, IL1 @ IL2))) .
	-- NEED TO MAKE SURE THAT THIS LAST RULE IS APPLIED WHEN NO OTHER SIMPLIFICATION IS POSSIBLE !
	eq simplify(N, IL) = (N, IL) .
	
	eq s-th(N,IL) = (nth(N,IL) = nth(1st(simplify(N,IL)),2nd(simplify(N,IL)))) .
}

open SIMPLIFY .
	ops il1 il2 il3 : -> IList .
	ops i1 i2 i3 i4 : -> Instr .
	ops n m : -> PNat .
	red simplify(len(il1) + n, il1 @ il2) .			-- OK
	red simplify(len(il1) + s(0), il1 @ il2) .		-- OK
	red simplify(n + len(il1), il1 @ il2) .			-- OK
	red simplify(n + len(il1) + m, il1 @ il2) .		-- OK
	red simplify(len(il1), il1 @ il2) .				-- OK
	red simplify(s(s(len(il1))), il1 @ il2) .		-- OK
	red simplify(s(s(len(il1))) + N, il1 @ il2) .	-- OK
	red simplify(s(s(len(il1) + N)), il1 @ il2) .	-- OK
	red simplify(s(s(len(il1) + len(il2) + N)), il1 @ il2 @ il3) .	-- OK
	red simplify(s(s(len(il1)) + len(il2)), il1 @ (i1 | il2) @ (i2 | i3 | il3)) .	-- OK
	red simplify(s(s(len(il2)) + len(il1)), il1 @ (i1 | il2) @ (i2 | i3 | il3)) .	-- OK
	red simplify(s(s(len(il2)) + len(il1)) + s(len(il3)), il1 @ (i1 | il2) @ (i2 | il3) @ (i3 | i4 | iln)) .	-- OK
close

-- ------------
-- S-THEOREM --
-- ------------

-- BASE CASE
open SIMPLIFY .
	op n : -> PNat .
	red s-th(n,iln) .
close

-- INDUCTION CASE
open SIMPLIFY .
	op n : -> PNat .
	op il : -> IList .
	op i : -> Instr .
	
	-- Induction hypothesis
	eq nth(N,il) = nth(1st(simplify(N,il)),2nd(simplify(N,il))) .
	
	red s-th(n,i | il) .
close