mod! PNAT principal-sort PNat {
	[PZero NzPNat < PNat]
	[PNat ErrPNat < PNat&Err]
	op 0 : -> PZero {constr} .
	op s : PNat -> NzPNat {constr} .
	op errPNat : -> ErrPNat {constr} .
	op if_then{_}else{_} : Bool PNat&Err PNat&Err -> PNat&Err .
	op _<_ : PNat PNat -> Bool .
	op _<_ : PNat&Err PNat&Err -> Bool .
	op _+_ : PNat PNat -> PNat .
	op _+_ : PNat&Err PNat&Err -> PNat&Err .
	op _*_ : PNat PNat -> PNat .
	op _*_ : PNat&Err PNat&Err -> PNat&Err .
	op sd : PNat PNat -> PNat .
	op sd : PNat&Err PNat&Err -> PNat&Err .
	op _quo_ : PNat NzPNat -> PNat .
	op _quo_ : PNat PZero -> ErrPNat .
	op _quo_ : PNat&Err PNat&Err -> PNat&Err .
	op _rem_ : PNat NzPNat -> PNat .
	op _rem_ : PNat PZero -> ErrPNat .
	op _rem_ : PNat&Err PNat&Err -> PNat&Err .
	
	-- equations
	vars M N : PNat . var NzN : NzPNat .
	vars ME NE : PNat&Err .
	
		-- properties of Peano numbers
		eq (s(N) = 0) = false .
		eq (s(N) = s(M)) = (N = M) .
		eq (errPNat = N) = false .
		
		-- Comparison and conditional statement
		eq if true then {NE} else {ME} = NE .
		eq if false then {NE} else {ME} = ME .
		eq (NE < errPNat) = false .
		eq (errPNat < NE) = false .
		eq (0 < NzN) = true .
		eq (N < 0) = false .
		eq (s(M) < s(N)) = (M < N) .
		
		-- arithmetic operations
		eq 0 + N = N .
		eq s(N) + M = s(N + M) .
		eq NE + errPNat = errPNat .
		eq errPNat + NE = errPNat .
		
		eq 0 * N = 0 .
		eq s(N) * M = (N * M) + M .
		eq NE * errPNat = errPNat .
		eq errPNat * NE = errPNat .
		
		eq sd(0,N) = N .
		eq sd(s(N),0) = s(N) .
		eq sd(s(N),s(M)) = sd(N,M) .
		eq sd(NE,errPNat) = errPNat .
		eq sd(errPNat,NE) = errPNat .
		
		eq 0 quo NzN = 0 .
		eq M quo NzN = if (M < NzN) then { 0 } else { s((sd(M,NzN) quo NzN)) } .
		eq M quo 0 = errPNat .
		eq NE quo errPNat = errPNat .
		eq errPNat quo NE = errPNat .
		
		eq 0 rem NzN = 0 .	
		eq M rem NzN = if (M < NzN) then { M } else { (sd(M,NzN) rem NzN) } .
		eq M rem 0 = errPNat .
		eq NE rem errPNat = errPNat .
		eq errPNat rem NE = errPNat .
}