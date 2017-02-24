mod! PAIR(FE :: TRIV, SE :: TRIV) {
	[Pair]
	op (_,_) : Elt.FE Elt.SE -> Pair {constr} .
}

mod! TRIPLE(FE :: TRIV, SE :: TRIV, TE :: TRIV) {
	[Triple]
	op (_,_,_) : Elt.FE Elt.SE Elt.TE -> Triple {constr} .
}

mod! TRIV-ERR {
	[Elt Err < Elt&Err]
	op err : -> Err .
}

mod! TRIV-ERR-IF {
	[Elt Err < Elt&Err]
	op err : -> Err .
	op if_then{_}else{_} : Bool Elt&Err Elt&Err -> Elt&Err .
}

mod! GLIST-ERR(E :: TRIV-ERR) {
	[Nil NnList < List]
	[List ErrList < List&Err]
	op errList : -> ErrList {constr} .
	op nil : -> Nil {constr} .
	op _|_ : Elt.E List -> List {constr} .
	op _|_ : Elt&Err.E List&Err -> List&Err .
	op _@_ : List List -> List .
	op _@_ : List&Err List&Err -> List&Err .
	op if_then{_}else{_}
	: Bool List&Err List&Err -> List&Err .
	var X : Elt.E .
	var XE : Elt&Err.E .
	vars L L2 : List .
	vars LE LE2 : List&Err .
	-- _|_
	eq err.E | LE = errList .
	eq XE | errList = errList .
	-- _@_
	eq nil @ L2 = L2 .
	eq (X | L) @ L2 = X | (L @ L2) .
	eq errList @ LE = errList .
	eq LE @ errList = errList .
	-- if_then{_}else{_}
	eq if true then {LE} else {LE2} = LE .
	eq if false then {LE} else {LE2} = LE2 .
}

mod! BOOL-ERR {
	[Bool ErrBool < Bool&Err]
	op errBool : -> ErrBool {constr} .
	op if_then{_}else{_} : Bool Bool Bool -> Bool .
	vars B1 B2 : Bool .
	-- if_then{_}else{_}
	eq if true then {B1} else {B2} = B1 .
	eq if false then {B1} else {B2} = B2 .
}

mod! ENTRY(K :: TRIV, V :: TRIV-ERR-IF) {
	pr(PAIR(K,V) * {sort Pair -> Entry})
	[Entry ErrEntry < Entry&Err]
	op errEntry : -> ErrEntry {constr} .
	op (_,_) : Elt.K Elt&Err.V -> Entry&Err .
	var K : Elt.K .
	eq (K,err.V) = errEntry .
}

mod! TABLE {
	pr(BOOL-ERR)
	pr(GLIST-ERR(E <= view from TRIV-ERR to ENTRY {sort Elt -> Entry,
				sort Err -> ErrEntry,
				sort Elt&Err -> Entry&Err,
				op err -> errEntry} )
		* {sort List -> Table, sort Nil -> EmpTable, sort NnList -> NeTable,
		sort ErrList -> ErrTable, sort List&Err -> Table&Err,
		op errList -> errTable, op nil -> empTable} ) .
	
	op singleton : Elt.K Elt.V -> Table .
	op singleton : Elt.K Elt&Err.V -> Table&Err .
	op isReg : Table Elt.K -> Bool .
	op isReg : Table&Err Elt.K -> Bool&Err .
	op lookup : Table Elt.K -> Elt&Err.V .
	op lookup : Table&Err Elt.K -> Elt&Err.V .
	op update : Table Elt.K Elt.V -> Table .
	op update : Table&Err Elt.K Elt&Err.V -> Table&Err .
	op insert : Table Elt.K Elt.V -> Table&Err .
	op insert : Table&Err Elt.K Elt&Err.V -> Table&Err .
	op remove : Table Elt.K -> Table .
	op remove : Table&Err Elt.K -> Table&Err .

	-- equations
	vars K K2 : Elt.K .
	vars V V2 : Elt.V .
	vars VE VE2 : Elt&Err.V .
	var T : Table .
	var TE : Table&Err .
	
	eq singleton(K,err.V) = errTable .
	eq singleton(K,V) = (K,V) | empTable .
	
	eq isReg(errTable,K2) = errBool .
	eq isReg(empTable,K2) = false .
	eq isReg((K,V) | T,K2) = if K == K2 then {true} else {isReg(T,K2)} .
	
	eq lookup(errTable,K2) = err.V .
	eq lookup(empTable,K2) = err.V .
	eq lookup((K,V) | T,K2) = if K == K2 then {V} else {lookup(T,K2)} .
	
	eq update(errTable,K2,VE2) = errTable .
	eq update(TE,K2,err.V) = errTable .
	eq update(empTable,K2,V2) = (K2,V2) | empTable .
	eq update((K,V) | T,K2,V2) = if K == K2 then {(K,V2) | T} else {(K,V) | update(T,K2,V2)} .
	
	eq insert(errTable,K2,VE) = errTable .
	eq insert(TE,K2,err.V) = errTable .
	eq insert(T,K2,V2) = if isReg(T,K2) then {errTable} else {(K2,V2) | T} .
	
	eq remove(errTable,K2) = errTable .
	eq remove(empTable,K2) = empTable .
	eq remove((K,V) | T,K2) = if K == K2 then {T} else {(K,V) | remove(T,K2)} .
}

mod! STRING-ERR principal-sort String {
	pr(STRING)
	[String ErrString < String&Err]
	op errStr : -> ErrString {constr} .
	op if_then{_}else{_} : Bool String&Err String&Err -> String&Err .
	vars SE1 SE2 : String&Err .
	eq if true then {SE1} else {SE2} = SE1 .
	eq if false then {SE1} else {SE2} = SE2 .
}

view TRIV2QID from TRIV to QID {
	sort Elt -> Qid
}

view TRIV-ERR-IF2STRING-ERR from TRIV-ERR-IF to STRING-ERR {
	sort Elt -> String,
	sort Err -> ErrString,
	sort Elt&Err -> String&Err,
	op err -> errStr,
	op (if_then{_}else{_}) -> (if_then{_}else{_}),
}

