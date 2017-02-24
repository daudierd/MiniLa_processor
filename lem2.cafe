-- ----------------------------------------------------------
--                                                         --
--       MiniLa language processor verified compiler       --
--                 PROOF  SCORES - LEMMA 2                 --
--                                                         --
--                     DAUDIER, Dorian                     --
--            Special research student at JAIST            --
--                                                         --
-- ----------------------------------------------------------

in calculator.mod
in del.mod

-- ----------
-- LEMMA 2 --
-- ----------

-- exec2(bjump(len(IL1) + N),IL,len(IL1) + PC,SE,EE) = exec2(bjump(N),IL,PC,SE,EE)

-- BASE CASE
open VERIFY-COMP .
	op il : -> IList .
	ops pc n : -> PNat .
	op s : -> Stack&Err .
	op ev : -> Env .
	
	-- check
	red lem2(n, iln, il, pc, s, ev) .
close

-- INDUCTION CASE
open VERIFY-COMP .
	ops il il1 : -> IList .
	op i : -> Instr .
	ops pc n : -> PNat .
	op s : -> Stack&Err .
	op ev : -> Env .
	
	-- IH
	eq exec2(bjump(len(il1) + n),IL,len(il1) + pc,s,ev) = exec2(bjump(n),il,pc,s,ev) .
	-- check
	red lem2(n, i | il1, il, pc, s, ev) .
	red lem2(n, i | il1, il, pc, s, errEnv) .
close

-- ------------
-- LEMMA 2-0 --
-- ------------

-- exec2(bjump(len(IL1)),IL,PC + len(IL1),SE,EE) = exec2(bjump(0),IL,PC,SE,EE)

open VERIFY-COMP .
	ops il il1 : -> IList .
	op pc : -> PNat .
	op s : -> Stack&Err .
	op ee : -> Env&Err .
	
	-- check
	red lem2(0, il1, il, pc, s, ee) implies lem2-0(il1, il, pc, s, ee) .
close
