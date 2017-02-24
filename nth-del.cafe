-- ----------------------------------------------------------
--                                                         --
--       MiniLa language processor verified compiler       --
--                  NTH-DEL THEOREM PROOF                  --
--                                                         --
--                     DAUDIER, Dorian                     --
--            Special research student at JAIST            --
--                                                         --
-- ----------------------------------------------------------

in del.mod

-- ------------------
-- Nth-del theorem --
-- ------------------

-- BASE CASE
open NTH-DEL .
	op il : -> IList .
	op i : -> Instr .
	
	-- check
	-- The result differs whether the list is empty (nth returns an error) or not, so we verify both cases
	red nthd-th(0, iln) .
	red nthd-th(0, i | il) .
close

-- INDUCTION CASE
open NTH-DEL .
	op il : -> IList .
	op i : -> Instr .
	op n : -> PNat .
	
	-- Induction Hypothesis
	eq nth(n, IL) = hd(del(n, IL)) .
	
	-- check
	-- Like base case, we verify two cases
	red nthd-th(s(n), iln) .
	red nthd-th(s(n), i | il) .
close