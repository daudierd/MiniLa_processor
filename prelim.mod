in calculator.mod

-- ----------
-- LEMMA 0 --
-- ----------

open VERIFY-COMP .
	op il : -> IList .
	-- check
	red lem0(iln, il) .
close

open VERIFY-COMP .
	ops il1 il2 : -> IList .
	op i : -> Instr .
	-- IH
	eq len(il1) + len(il2) = len(il1 @ il2) .
	-- check
	red lem0(i | il1, il2) .
close

-- ------------
-- lemma Pev --
-- ------------

open VERIFY-COMP .
	op ev : -> Env .
	-- check
	red lemPev(0, ev) .
close

open VERIFY-COMP .
	op en : -> ExpPNat .
	op ev : -> Env .
	-- IH
	eq evalExp(en, EV) = en2n(en) .
	-- check
	red lemPev(s(en), ev) .
close

-- ------------
-- lemma Iln --
-- ------------

open VERIFY-COMP .
	-- check
	red lemIln(iln) .
close

open VERIFY-COMP .
	op il : -> IList .
	op i : -> Instr .
	-- IH
	eq il @ iln = il .
	-- check
	red lemIln(i | il) .
close