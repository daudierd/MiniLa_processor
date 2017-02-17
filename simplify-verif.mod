in calculator.mod

mod! NTHPAIR {
	pr(PAIR(PNAT, ILIST) * { sort Pair -> NthPair })
	op s : NthPair -> NthPair .
	op _=_ : NthPair NthPair -> Bool .
	op 1st : NthPair -> PNat .
	op 2nd : NthPair -> IList .
	
	vars N N1 N2 : PNat . vars IL IL1 IL2 : IList .
	vars NP1 NP2 : NthPair .
	eq s(N,IL) = (s(N), IL) .
	eq ((N1,IL1) = (N2,IL2)) = N1 = N2 and IL1 = IL2 .
	eq 1st(N,IL) = N .
	eq 2nd(N,IL) = IL .
}

mod! SIMPLIFY { pr(PNAT) pr(ILIST) pr(NTHPAIR) pr(VM)
	op simplify : NthPair -> NthPair {strat (0 1 0)} .	-- this strategy is necessary to reduce the 2nd case following module definition
	-- lemmas & properties
	op lm1 : IList IList -> Bool .
	op lm2 : PNat IList IList -> Bool .
	op lm3 : PNat IList -> Bool .
	op lm4 : PNat PNat IList -> Bool .
	op p1 : PNat PNat IList -> Bool .
	op p2 : PNat IList IList -> Bool .
	op s-th : PNat IList -> Bool .
	
	vars IL IL1 IL2 : IList . vars N M : PNat . var I : Instr .
	-- simplification equations
	eq simplify(0, IL) = (0, IL) .
	eq simplify(s(N), iln) = (s(N), iln) .
	eq simplify(s(N), I | IL) = simplify(N, IL) .
	
	-- lemmas
	eq lm1(IL1,IL2) = (simplify(len(IL1), IL1 @ IL2) = (0, IL2)) .
	eq lm2(N,IL1,IL2) = (simplify(len(IL1) + N, IL1 @ IL2) = simplify(N, IL2)) .
	eq lm3(M,IL) = (simplify(s(M), IL) = simplify(s(simplify(M, IL)))) .
	eq lm4(M,N,IL) = (simplify(s(M) + N, IL) = simplify(s(simplify(M + N, IL)))) .
	
	-- properties (facultative)
	eq p1(M,N,IL) = (simplify(M,IL) = (N,iln) implies M = N + len(IL)) .
	eq p2(M,IL1,IL2) = (simplify(M,IL1) = (0,IL2) implies len(IL1) = len(IL) + M) .
	
	eq s-th(N,IL) = (nth(N,IL) = nth(1st(simplify(N,IL)),2nd(simplify(N,IL)))) .
}

-- ----------
-- LEMMA 1 --
-- ----------

-- BASE CASE
open SIMPLIFY .
	op il : -> IList .
	-- check
	red lm1(iln,il) .
close

-- INDUCTION CASE
open SIMPLIFY .
	ops il1 il2 : -> IList .
	op i : -> Instr .
	-- Induction hypothesis
	eq simplify(len(il1), il1 @ il2) = (0, il2) .
	-- check
	red lm1(i | il1, il2) .
close

-- ----------
-- LEMMA 2 --
-- ----------

-- BASE CASE
open SIMPLIFY .
	op il : -> IList .
	op n : -> PNat .
	-- check
	red lm2(n,iln,il) .
close

-- INDUCTION CASE
open SIMPLIFY .
	ops il1 il2 : -> IList .
	op i : -> Instr .
	op n : -> PNat .
	-- Induction hypothesis
	eq simplify(len(il1) + N, il1 @ IL2) = simplify(N, IL2) .
	-- check
	red lm2(n, i | il1, il2) .
close

-- ---------
-- PROP 1 --
-- ---------

-- simplify(M,IL) = (N,iln) implies M = N + len(IL)

-- BASE CASE
open SIMPLIFY .
	ops m n : -> PNat .
	op il : -> IList .
	-- check
	red (simplify(0,iln) = (n,iln) implies 0 = n + 0) .
	red (simplify(s(m),iln) = (n,iln) implies s(m) = n + 0) .
close

-- INDUCTION CASE
open SIMPLIFY .
	ops m n : -> PNat .
	op il : -> IList .
	op i : -> Instr .
	-- check
	red p1(m, n, il) implies p1(s(m), n, i | il) .
	-- IS IT SUFFICIENT?
	-- WE HAVEN'T CONSIDERED THE CASE (m = 0) BECAUSE WE KNOW IT IS IMPOSSIBLE
close

-- ---------
-- PROP 2 --
-- ---------

-- simplify(M,IL1) = (0,IL2) implies len(IL1) = len(IL) + M

-- PRELIMINARY
open SIMPLIFY .
	ops il1 il2 : -> IList .
	-- preliminary
	eq il1 = il2 .
	-- check
	red len(il1) = len(il2) .
close

-- BASE CASE
open SIMPLIFY .
	op m : -> PNat .
	ops il1 il2 : -> IList .
	-- preliminary
	eq ((IL1 = IL2) implies (len(IL1) = len(IL2))) = true .
	-- check: A => C and C => B 
	red (simplify(0,il1) = (0,il2) implies il1 = il2) .
	red (il1 = il2 implies len(il1) = len(il2)) .
close

-- INDUCTION CASE
open SIMPLIFY .
	op m : -> PNat .
	ops il1 il2 : -> IList .
	op i : -> Instr .
	-- check
	red p2(m, il1, il2) implies p2(s(m), i | il1, il2) .
close

-- ----------
-- LEMMA 3 --
-- ----------

-- simplify(s(M), IL) = simplify(s(simplify(M, IL)))

-- BASE CASE
open SIMPLIFY .
	op il : -> IList .
	-- check
	red lm3(0,il) .
close

-- INDUCTION CASE
open SIMPLIFY .
	op il : -> IList .
	op i : -> Instr .
	ops m : -> PNat .
	
	-- check
	--   CASE 1 - IL != iln
		-- lm3(s(m), i | il) LHS rewriting
	red simplify(s(s(m)), i | il) = simplify(s(m), il) .
		-- IH allows further rewriting of LHS
	red lm3(m, il) implies simplify(s(m), il) = simplify(s(simplify(m, il))) .
		-- LHS rewritten with IH is equal to lm3(s(m), i | il) RHS
	red simplify(s(simplify(m, il))) = simplify(s(simplify(s(m), i | il))) .
	
	--   CASE 2 - IL = iln
	red lm3(s(m),iln) .
close

-- ----------
-- LEMMA 4 --
-- ----------

-- simplify(s(M) + N, IL) = simplify(s(simplify(M + N, IL)))

-- DEDUCTION FROM LEMMA 3
open SIMPLIFY .
	op il : -> IList .
	ops m n : -> PNat .
	-- lemma 3
	eq simplify(s(M), IL) = simplify(s(simplify(M, IL))) .
	-- check
	red lm4(m,n,il) .
close


-- ------------
-- S-THEOREM --
-- ------------

-- nth(N,IL) = nth(1st(simplify(N,IL)),2nd(simplify(N,IL)))

-- BASE CASES
open SIMPLIFY .
	op il : -> IList .
	op n : -> PNat .
	-- check
	red s-th(0,il) .
	red s-th(n,iln) .
close

-- INDUCTION CASE
open SIMPLIFY .
	op n : -> PNat .
	op il : -> IList .
	op i : -> Instr .
	
	-- Induction hypothesis
	eq nth(n,IL) = nth(1st(simplify(n,IL)),2nd(simplify(n,IL))) .
	
	red s-th(s(n), i | il) .
	red s-th(s(n),iln) .
close
