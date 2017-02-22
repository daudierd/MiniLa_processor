-- ----------------------------------------------------------
--                                                         --
--       MiniLa language processor verified compiler       --
--          PRACTICAL DEFINITION OF DEL OPERATOR           --
--                                                         --
--                     DAUDIER, Dorian                     --
--            Special research student at JAIST            --
--                                                         --
-- ----------------------------------------------------------

in calculator.mod

mod! DEL {
	pr(COMP)
	pr(VM)
	
	op tl : NnIList -> IList .
	op tl : Iln -> ErrIList .
	op tl : IList&Err -> IList&Err .	
	op del : PNat IList&Err -> IList&Err .
	
	-- definition
	var N : PNat . vars IL IL1 IL2 : IList . var I : Instr .
	eq tl(errIList) = errIList .
	eq tl(iln) = errIList .
	eq tl(I | IL) = IL .
	
	eq del(N, iln) = errIList .
	eq del(0, IL) = IL .
	eq del(s(N), I | IL) = del(N, IL) .
	
	-- equations proved in del_verif.mod
	eq tl(del(N, I | IL)) = del(N, IL).					-- lem0
	eq del(s(N), IL) = tl(del(N, IL)) .					-- lem1
	eq del(s(N), IL1 @ IL2) = tl(del(N, IL1 @ IL2)) .	-- lem2
	eq del(len(IL1) + N, IL1 @ IL2) = del(N, IL2) .		-- lem3
	eq del(len(IL1), IL1 @ IL2) = del(0, IL2) .			-- lem3-0
}

mod! NTH-DEL {
	pr(DEL)
	
	-- Nth-del theorem
	-- The nth instruction of a list is the head instruction of the sublist obtained by removing the N first instructions (the first instruction being 0)
	op nthd-th : PNat IList -> Bool .
	
	var N : PNat . var IL : IList .
	eq nthd-th(N, IL) = (nth(N, IL) = hd(del(N, IL))) .
}
