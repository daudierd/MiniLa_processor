mod! DEL {
	pr(COMP)
	pr(VM)
	
	op tl : IList&Err -> IList&Err .
	op del : PNat IList -> IList .
	op del : PNat&Err IList&Err -> IList&Err .
	
	var N : PNat . var NE : PNat&Err .
	vars IL IL1 IL2 : IList . var I : Instr .
	eq tl(errIList) = errIList .
	eq tl(iln) = errIList .
	eq tl(I | IL) = IL .
	
	eq del(errPNat, IL) = errIList .
	eq del(NE, errIList) = errIList .
	eq del(N, iln) = errIList .
	eq del(0, IL) = IL .
	eq del(s(N), I | IL) = del(N, IL) .
	
	-- subsequently proved equations
	eq del(s(N), IL1 @ IL2) = tl(del(N, IL1 @ IL2)) .
	eq tl(del(N, I | IL)) = del(N, IL).
	eq del(len(IL1) + N, IL1 @ IL2) = del(N, IL2) . 
	eq del(len(IL1), IL1 @ IL2) = del(0, IL2) .
	
	-- Nth-del theorem
	op nthd-th : PNat IList -> Bool .
	eq nthd-th(N, IL) = (nth(N, IL) = hd(del(N, IL))) .
}

open DEL .
	ops il il1 il2 : -> IList .
	ops i i1 i2 : -> Instr .
	
	red del(s(len(il1)), (i1 | il1) @ il) = il .
	red del(s(s(len(il1))), (i1 | il1) @ (i2 | il)) = il .
	red del(s(s(s(len(il1)))), (i | i1 | i2 | il1) @ il) = il .
	red del(s(s(s(len(il1)))), (i | i1 | il1) @ (i2 | il)) = il .
	red del(s(s(s(len(il1)))), (i1 | il1) @ (i | i2 | il)) = il .
	red del(s(s(s(len(il1)))), il1 @ (i | i1 | i2 | il)) = il .
	red del(s(s(len(il1) + len(il2))), (i1 | il1) @ (i2 | (il2 @ il))) = il .
	red del(s(s(len(il1) + len(il2))), (i1 | i2 | il1) @ (il2 @ il)) = il .
close

-- ------------------
-- Nth-del theorem --
-- ------------------

-- BASE CASE
open DEL .
	op il : -> IList .
	op i : -> Instr .
	
	-- check
	red nthd-th(0, i | il) .
	red nthd-th(0, iln) .
close

-- INDUCTION CASE
open DEL .
	op il : -> IList .
	op i : -> Instr .
	op n : -> PNat .
	
	-- IH
	eq nth(n, IL) = hd(del(n, IL)) .
	
	-- check
	red nthd-th(s(n), i | il) .
	red nthd-th(s(n), iln) .
close

-- *********************************************
-- ************ FORMAL PROOF OF DEL ************
-- *********************************************

mod! DEL-FM {
	pr(COMP)
	pr(VM)

	op tl : IList&Err -> IList&Err .
	op del : PNat IList -> IList .
	op del : PNat&Err IList&Err -> IList&Err .

	var NE : PNat&Err . var N : PNat . vars IL IL1 IL2 : IList . var I : Instr .
	eq tl(errIList) = errIList .
	eq tl(iln) = errIList .
	eq tl(I | IL) = IL .
	
	eq del(errPNat, IL) = errIList .
	eq del(NE, errIList) = errIList .
	eq del(N, iln) = errIList .
	eq del(0, IL) = IL .
	eq del(s(N), I | IL) = del(N, IL) .
	
	-- equations to prove
	op lem0 : PNat Instr IList -> Bool .
	op lem1 : PNat IList -> Bool .
	op lem2 : PNat IList IList -> Bool .
	op lem3 : PNat IList IList -> Bool .
	op lem3-0 : IList IList -> Bool .
	
	eq lem0(N, I, IL) = (tl(del(N, I | IL)) = del(N, IL)) .
	eq lem1(N, IL) = (del(s(N), IL) = tl(del(N, IL))) .
	eq lem2(N, IL1, IL2) = (del(s(N), IL1 @ IL2) = tl(del(N, IL1 @ IL2))) .
	eq lem3(N, IL1, IL2) = (del(len(IL1) + N, IL1 @ IL2) = del(N, IL2)) . 
	eq lem3-0(IL1, IL2) = (del(len(IL1), IL1 @ IL2) = del(0, IL2)) . 
}

-- ----------
-- LEMMA 0 --
-- ----------

-- BASE CASE
open DEL-FM .
	op il : -> IList .
	op i : -> Instr .
	
	red lem0(0, i, il) .
close

-- INDUCTION CASE
open DEL-FM .
	op il : -> IList .
	ops i1 i2 : -> Instr .
	op n : -> PNat .
	
	-- IH
	eq tl(del(n, I | IL)) = del(n, IL) .
	
	-- check
	red lem0(s(n), i1, iln) .
	red lem0(s(n), i1, i2 | il) .
close

-- ----------
-- LEMMA 1 --
-- ----------

-- BASE CASE
open DEL-FM .
	op il : -> IList .
	op i : -> Instr .
	
	red lem1(0, iln) .
	red lem1(0, i | il) .
close

-- INDUCTION CASE
open DEL-FM .
	op il : -> IList .
	op i : -> Instr .
	op n : -> PNat .
	
	-- IH
	eq del(s(n), IL) = tl(del(n, IL)) .
	
	-- lemma 0
	eq tl(del(N, I | IL)) = del(N, IL) .
	
	-- check
	red lem1(s(n), iln) .
	red lem1(s(n), i | il) .
close

-- ----------
-- LEMMA 2 --
-- ----------

open DEL-FM .
	ops il1 il2 : -> IList .
	op n : -> PNat .
	
	red lem1(n, il1 @ il2) implies lem2(n, il1, il2).
close

-- ----------
-- LEMMA 3 --
-- ----------

-- del(len(IL1) + N, IL1 @ IL2) = del(N, IL2)

-- BASE CASE
open DEL-FM .
	op il : -> IList .
	op n : -> PNat .
	
	red lem3(n, iln, il) .
close

-- INDUCTION CASE
open DEL-FM .
	ops il1 il2 : -> IList .
	op i : -> Instr .
	op n : -> PNat .
	
	-- IH
	eq del(len(il1) + N, il1 @ IL2) = del(N, IL2) .
	
	-- check
	red lem3(n, i | il1, il2) .
close

-- ------------
-- LEMMA 3-0 --
-- ------------

open DEL-FM .
	ops il1 il2 : -> IList .
	
	red lem3(0, il1, il2) implies lem3-0(il1, il2) .
close