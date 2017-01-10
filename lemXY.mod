-- ----------------------------------------------------------
--                                                         --
--       MiniLa language processor verified compiler       --
--                 PROOF  SCORES - LEMMA 1                 --
--                                                         --
--                     DAUDIER, Dorian                     --
--            Special research student at JAIST            --
--                                                         --
-- ----------------------------------------------------------

in calculator.mod

-- ------------
-- LEMMA X-0 --
-- ------------

-- BASE CASE
open VERIFY-COMP .
	ops il : -> IList .
	-- check
	red lemX-0(iln, il) .
close

-- INDUCTION CASE
open VERIFY-COMP .
	ops il1 il2 : -> IList .
	op i : -> Instr .
	-- IH
	eq nth(len(il1), il1 @ il2) = nth(0, il2) .
	-- check
	red lemX-0(i | il1, il2) .
close

-- ------------
-- LEMMA X-1 --
-- ------------

-- BASE CASE
open VERIFY-COMP .
	ops il : -> IList .
	-- check
	red lemX-1(iln, il) .
close

-- INDUCTION CASE
open VERIFY-COMP .
	ops il1 il2 : -> IList .
	op i : -> Instr .
	-- IH
	eq nth(s(len(il1)), il1 @ il2) = nth(s(0), il2) .
	-- check
	red lemX-1(i | il1, il2) .
close

-- ------------
-- LEMMA Y-0 --
-- ------------

-- BASE CASE
open VERIFY-COMP .
	op inst : -> Instr .
	-- check
	red lemY-0(iln, inst) .
close

-- INDUCTION CASE
open VERIFY-COMP .
	op il : -> IList .
	ops i inst : -> Instr .
	-- IH
	eq len(il @ (inst | iln)) = s(len(il)) .
	-- check
	red lemY-0(i | il, inst) .
close

-- ------------
-- LEMMA Y-1 --
-- ------------

-- Proving lemY as a special case of lemY-0
open VERIFY-COMP .
	op i : -> Instr .
	ops il1 il2 : -> IList .
	op e : -> Exp .
	
	eq [:nonexec] : lemY-0(IL:IList, I:Instr) = true .
	eq il2 = il1 @ genExp(e) .
	
	-- check
	red lemY-0(il2, i) implies lemY-1(il1, i, e) .
close

-- ------------
-- LEMMA Y-2 --
-- ------------

-- Proving lemY as a special case of lemY-0
open VERIFY-COMP .
	op i : -> Instr .
	ops il1 il2 : -> IList .
	ops e1 e2 : -> Exp .
	
	eq [:nonexec] : lemY-0(IL:IList, I:Instr) = true .
	eq il2 = il1 @ genExp(e1) @ genExp(e2) .
	
	-- check
	red lemY-0(il2, i) implies lemY-2(il1, i, e1, e2) .
close