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
	
	eq s-th(N,IL) = (nth(N,IL) = nth(1st(simplify(N,IL)),2nd(simplify(N,IL)))) .
}

-- -------------
-- Equation 1 --
-- -------------

-- simplify(len(IL1) + N, IL1 @ IL2) = simplify(N, IL2)


open SIMPLIFY .
	op n : -> PNat .
	op il : -> IList .
	-- check
	red simplify(len(iln) + n, iln @ il) = simplify(n, il) .
close

open SIMPLIFY .
	op n : -> PNat .
	op i : -> Instr .
	ops il1 il2 : -> IList .
	-- IH
	eq simplify(len(il1) + n, il1 @ il2) = simplify(n, il2) .	
	-- check
	red simplify(len(i | il1) + n, (i | il1) @ il2) = simplify(n, il2) .
close

-- -------------
-- Equation 2 --
-- -------------

-- simplify(s(M) + N, IL1 @ IL2) = simplify(s(simplify(M + N, IL1 @ IL2)))

open SIMPLIFY .
	op n : -> PNat .
	ops il1 il2 : -> IList .
	-- check
	red simplify(s(0) + n, il1 @ il2) = simplify(s(simplify(0 + n, il1 @ il2))) .
close
