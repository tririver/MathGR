(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`tensor`"]

DeclareIdx::usage = "DeclareIdx[ids_List, dim, set, color] defines dim, which set of idx to use and color for a pair of indices (upper, lower)"
DeclareExplicitIdx::usage = "DeclareExplicitIdx[ids_List, color] defines a pair of explicit index and display color"
IdxList::usage = "A list of index identifiers with Einstein sum convention"
IdxPtn::usage = "A pattern object to label index identifiers with Einstein sum convention"
IdxUpList::usage = "A list of upper index identifiers with Einstein sum convention"
IdxUpPtn::usage = "A pattern object to label upper index identifiers with Einstein sum convention"
IdxDnList::usage = "A list of lower index identifiers with Einstein sum convention"
IdxDnPtn::usage = "A pattern object to label lower index identifiers with Einstein sum convention"
IdxNonSumList::usage = "A list of index identifiers with Einstein sum convention"
IdxNonSumPtn::usage = "A pattern object to label index identifiers without Einstein sum convention"
IdxDual::usage = "IdxDual[identifier] gives dual index. E.g. IdxDual[UP] gives DN."
IdxSet::usage = "Set of indices to use for a identifiers"
IdxColor::usage = "IdxColor[idx] gives color for given idx"

Dim::usage = "Dim[id] returns dimension associated with tensor index"
DefaultDim::usage = "Default dimension of the tensors (with UP and DN)"

UP::usage = "Default upper idx prefix"
DN::usage = "Default lower idx prefix"
UE::usage = "Explicit upper idx prefix"
DE::usage = "Explicit lower idx prefix"

Uq::usage = "Uq[n] generates a sequence of Unique[] of length n"
Sym::usage = "Sym[expr, {a, b, ...}] symmetrizes indices a, b, ... Sym[expr] symmetrizes all free indices"
Asym::usage = "ASym[expr, {a, b, ...}] anti-symmetrizes indices a, b, ... Asym[expr] anti-symmetrizes all free indices"

Dta::usage = "Delta symbol"
DtaGen::usage = "DtaGen[up..., dn...] is the generalized delta symbol"
Pd::usage = "Pd[f, DN@a] is partial derivative"
LeviCivita::usage = "LeviCivita[a, b, ...] is the Levi Civita tensor, defined only if dimension is given as an explicit number"

LatinIdx::usage = "strings {a, b, ..., }"
GreekIdx::usage = "strings {alpha, beta, ...}"
LatinCapitalIdx::usage = "strings {A, B, ...}"
UniqueIdx::usage = "unique vars {$n1, $n2, ...}"

DeclareSym::usage = "Declare tensor symmetry"
Simp::usage = "Default simplification, with SimpHook applied"
SimpUq::usage = "Simp, keeping dummy unique"
SimpHook::usage = "Rules to apply before and after Simp"
simpMSelect::usage = "A function to select terms to simplify, disregard others."

\[Bullet]::usage = "Symbol for time derivative"

Begin["`Private`"]
Needs["MathGR`utilPrivate`"]

Uq[n_Integer]:= Sequence@@Table[Unique[],{n}]


(* ::Section:: *)
(* Idx utilities *)

LatinIdx = Join[FromCharacterCode /@ Range[97, 97 + 24], "y"<>ToString[#]&/@Range[26]]
GreekIdx = Join[FromCharacterCode /@ Range[945, 945 + 24], "\[Omega]"<>ToString[#]&/@Range[26]]
LatinCapitalIdx = Join[FromCharacterCode /@ Range[65, 65 + 24], "Y"<>ToString[#]&/@Range[26]]
UniqueIdx:= Unique[]& /@ Range[50]

SetAttributes[Dta, Orderless]
Pd[Dta[__],_]:= 0

Options[DtaGen]={"DtaGenDta"->Dta}
DtaGen[ids:(_[_]..), OptionsPattern[]]:= Module[{btmp, tmp, i, d=Length[{ids}]/2, a, b},
	a = Take[{ids}, d]; b = Take[{ids}, -d]; 
	btmp = MapThread[#1[#2] &, {(b[[#]][[0]] & /@ Range[d]), tmp /@ Range[d]}];
	Asym[Product[OptionValue["DtaGenDta"][a[[i]], btmp[[i]]], {i, d}],btmp]/. (btmp[[#]]->b[[#]] &/@Range[d])//ReleaseHold]

DeclareIdx[ids_List, d_, set_, color_]:= Module[{idsAlt=Alternatives@@ids}, Pd[d,_]:=0;
	Dim[idsAlt]:=d; IdxSet[idsAlt]:=set; IdxColor[idsAlt]:=color; add2set[IdxList, {ids}]; IdxPtn=Alternatives@@(Blank/@IdxList);
	IdxDual[ids[[1]]]=ids[[2]];	IdxDual[ids[[2]]]=ids[[1]];
	add2set[IdxUpList,ids[[1]]]; IdxUpPtn=Alternatives@@(Blank/@IdxUpList);
	add2set[IdxDnList,ids[[2]]]; IdxDnPtn=Alternatives@@(Blank/@IdxDnList);
	Dta[idsAlt@a_, idsAlt@a_]:= d;
	Dta/:Power[Dta[idsAlt@a_, idsAlt@b_], 2]:= d;
	Dta/:Dta[(a:idsAlt)@m_, (b:idsAlt)@n_] f_ := Piecewise[{{ReleaseHold[f/.idsAlt@n -> a@m], !FreeQ[f, idsAlt@n]}, 
		{ReleaseHold[f/.idsAlt@m -> b@n], !FreeQ[f, idsAlt@m]}},	Hold[Dta][a@m, b@n] f];
	If[IntegerQ[d],
		DeclareSym[LeviCivita, ConstantArray[#, d], Antisymmetric[All]]& /@ ids;
		LeviCivita /: LeviCivita[a:(ids[[1]][_]..)]*LeviCivita[b:(ids[[2]][_]..)]:= DtaGen[a,b];  ]]

DeclareExplicitIdx[ids_List, color_]:= Module[{}, 
	(IdxColor[#]:=color; add2set[IdxNonSumList, #]; IdxNonSumPtn=Alternatives@@(Blank/@IdxNonSumList))&/@ids;
	Dta[(Alternatives@@ids)@i_, (Alternatives@@ids)@j_]:= KroneckerDelta[i, j]]

DeclareIdx[{UP, DN}, DefaultDim, GreekIdx, Black]
DeclareExplicitIdx[{UE, DE}, Gray]

idx:= Cases[times2prod@#,a:IdxPtn:>a[[1]],Infinity]& (* only find indices with Einstein convention *)
free:= Cases[Tally[idx@#], {a_,1}:>a] &
freeFull[e_]:= Cases[e, a:IdxPtn/;MemberQ[free@e, a[[1]]]:>a, Infinity]
dummy:= Cases[Tally[idx@#], {a_,2}:>a] &
getFreeSample:= free[getSampleTerm@#]&

Sym[e_, iList_]:= Plus@@ ( (e/.(iList~replaceTo~#)&) /@ Permutations[iList] )
Asym[e_, iList_]:= Plus@@ ( (Signature[#] e/.(iList~replaceTo~#)&) /@ Permutations[iList] )
Sym[e_]:= Sym[e, free@e]
Asym[e_]:= Asym[e, free@e]  

(* ::Section:: *)
(* Partial derivative *)

Pd[a_Plus, i_]:= Pd[#,i]& /@ a;
Pd[a_*b_, i_]:= Pd[a,i]*b + a*Pd[b,i];
Pd[f_^g_, i_]:= f^(g-1)*g*Pd[f,i] + f^g*Log[f]*Pd[g,i];
Pd[a_?NumericQ, i_]:=0;
Pd[Pd[a_, i_], j_]/;!OrderedQ[{i,j}]:=Pd[Pd[a, j], i];

pd2pdts[expr_]:= Module[{ip=IdxPtn|IdxNonSumPtn}, 
	expr/.{f:_Pd :> pdts[Count[{f}, Pd[_,_], Infinity]][f//.{Pd[e_,ip]:>e, x_[ip..]:>x}][Sequence@@Cases[f,ip,Infinity]]}]
pdts2pd = #/.pdts[n_][f_][idx__] :> Fold[Pd, If[n===Length[{idx}], f, f[Sequence @@ Take[{idx}, Length@{idx} - n]]], Take[{idx}, -n]] &

(* ::Section:: *)
(* Simp functions *)

sumAlt:=Alternatives@@IdxList;

rmNE[e_] := DeleteCases[e, IdxNonSumPtn];
addAss[cond_]:= $Assumptions=Simplify[$Assumptions&&cond,Assumptions->True]
DeclareSym[t_,idx_,sym_]:= (If[sym===Symmetric[All]||sym==={Symmetric[All]}, SetAttributes[t, Orderless]];
	addAss[MAT[t][Sequence@@idx]~Element~Arrays[Dim/@rmNE[idx], sym]];)

simpFterm[t_, fr_]:= Module[{dum, availDum, rule, a0},
	dum = dummy@t;
	availDum = Take[Complement[LatinIdx, fr], Length@dum];
	rule = replaceTo[(a0:sumAlt)/@dum, a0/@availDum];
	t /. rule]
simpF[e_]:= Module[{eList},
	eList = ReleaseHold@plus2list@ReleaseHold@e;
	Total[simpFterm[#, Sort@free@eList[[1]]]& /@ eList]] 

simpH::ver="Warning: Mathematica version 8 or lower detected. Simp may not bring tensor to unique form"
simpH = If[$VersionNumber>8.99, simpM[simpF@#]&, Message[simpH::ver]; simpF]

If[!ValueQ@SimpHook,SimpHook = {}]

Options[Simp]= {"Method"->"Hybrid"}
Simp[e_, OptionsPattern[]]:= Switch[OptionValue["Method"], "Fast", simpF, "MOnly", simpM, _, simpH][e//.SimpHook]//.SimpHook//Expand
Options[SimpUq]= {"Method"->"Hybrid"}
SimpUq[e_, OptionsPattern[]]:= Block[{IdxSet}, (IdxSet[#]=IdxSet[IdxDual[#]]=UniqueIdx)&/@DeleteDuplicates[IdxList, IdxDual[#1] == #2 &]; Simp[e, "Method"->OptionValue["Method"]]]

(* ::Section:: *)
(* M-backend of Simp *)

simpMTermAss[tM_]:= Module[{tInPdts, ass, cnt},
	(* Add assumptions for tensors encountered in each term *)
	ass = And@@Cases[{tM},f:MAT[t_][idx__]:>(f~Element~Arrays[Dim/@rmNE[{idx}]]), Infinity];
	(* Add symmetry of T in PdPdPdT *)
	tInPdts = Cases[{tM}, HoldPattern[f:MAT[pdts[n_][t_]][idx__]] :>
		{MAT[t][Sequence@@Take[{idx},Length[{idx}]-n]],f,Dim/@rmNE[{idx}]}, Infinity];
	ass = ass && And@@Flatten[Cases[$Assumptions,#[[1]]~Element~HoldPattern[Arrays[dim_,dom_,sym_]]:>
		#[[2]]~Element~Arrays[#[[3]],dom,sym],Infinity]&/@tInPdts];
	(* Add symmetry of PdPdPd in PdPdPdT *)
	ass = ass && And@@Flatten@Cases[{tM},f:MAT[pdts[n_][t_]][idx__] /; n>1 :> ((f~Element~Arrays[Dim/@rmNE[{idx}], Symmetric[#]])& 
		/@ (cnt=Length[{idx}]-n; Split[Cases[Take[{idx},-n],sumAlt],Function[{x,y},Dim[x]==Dim[y]]]/.{s:(sumAlt):> ++cnt})), Infinity] ]

simpM::ld="Warning: Memory constraint reached in `1`, simplification skipped"
tReduceMaxMemory=10^9 (* 1GB max memory *)
tReduce[e_]:= MemoryConstrained[TensorReduce[e], tReduceMaxMemory, Message[simpM::ld, term];e]

simpMTerm[term_, fr_, dum_, x_]:=Module[{t, tCt, tM, xFr, slots, tNewIdx, cnt, cntId, slot1, slot2, oldDummy=dummy@term},
	If[oldDummy==={}&&fr==={}, Return[term]]; (* no idx *)
	t = x ~TensorProduct~ times2prod[term, TensorProduct]; (* Add tensor product and contraction tensor *)
	tCt = Map[Flatten@Position[idx@t,#]&, fr~Join~oldDummy]; (* Determine contraction pairs *)
	tM = t /. id:IdxPtn:>id[[0]] /. f_[id__]:>MAT[f][id] /; !FreeQ[{id},sumAlt,1]; (* The tensor to input to TensorReduce *)
	tM = times2prod[Assuming[simpMTermAss[tM], Expand@tReduce@TensorContract[tM, tCt]], List]; (* Outcome from TensorReduce *)
	If[tM===0, Return[0]]; 
	tCt = Cases[{tM}, TensorContract[f_,cts_]:> cts, Infinity]; (* Get new contraction pairs *)
	cnt=0; tCt = Sequence@@(#+(cnt=cnt+2*Length@#)-2*Length@#)&/@tCt; (* Apply adjustments (if multiple TensorContract[], shift contraction pair) *)
	cnt=1; slots = rmNE@( tM//Cases[{#},MAT[a_][i__]:>If[a===xMat,Sequence@@({i}/.(sumAlt):>xFr[cnt++]),Sequence@@{i}],Infinity]& ); (* Get tensor slots *)
	(cntId[#]=1)& /@IdxList; (* Initialize counter for each index *) 
	tNewIdx = ((	slot1=slots[[#[[1]]]];		slot2=slots[[#[[2]]]];
		Piecewise[{	(* Assign free and newDummy to tensor slots *)
			{ {{#[[1]],fr[[Plus@@slot1]]},{#[[2]],fr[[Plus@@slot1]]}}, Head@slot1===xFr},
			{ {{#[[1]],fr[[Plus@@slot2]]},{#[[2]],fr[[Plus@@slot2]]}}, Head@slot2===xFr}},
			{{#[[1]],dum[slot1][[cntId[slot1]]]},{#[[2]],dum[slot2][[cntId[IdxDual@slot1]++;cntId[slot1]++]]}}]
		)& /@ tCt // Flatten[#,1]& // Sort // Transpose)[[2]];
	cnt=1; tM /. TensorContract[a_,i_]:>a /. MAT[f_]:>f /. id:sumAlt|xFr:>id@tNewIdx[[cnt++]] /._xMat->1 //prod2times[#,TensorProduct|List]& (* Put idx back *)]

If[!ValueQ@simpMSelect,simpMSelect = Identity]
simpMHook:= {{ReleaseHold (*here eval first*), plus2list, simpMSelect, pd2pdts, ReleaseHold (*here eval last*)}, {pdts2pd, simpMSelect,Total}}
simpM[e_]:= Module[{eList = Fold[#2[#1]&, e, simpMHook[[1]]](* apply init hook *), fr, dum, x},
	If[eList=={}, Return[0]]; (* simpMSelect may return empty list *)
	fr = Sort@free@eList[[1]]; 
	x = If[fr==={}, 1, xMat@@(Function[i, Operate[IdxDual,i]]/@ SortBy[freeFull@eList[[1]], #[[1]]&]) ]; (* contraction tensor *) 
	(dum[#] = Complement[IdxSet[#], fr]) & /@ IdxList; (* Available free idx for each identifier *)
	Fold[#2[#1]&, simpMTerm[#,fr,dum,x]&/@eList, simpMHook[[2]]] (* Apply ending hook and return result *) ]


(* ::Section:: *)
(* Check tensor validity at $Pre *)

preCheckList = {checkNestIdx, checkDummyIdx}

$PreRead::nestidx = "Nested indices are not allowed in `1`."
checkNestIdx = Module[{t=Cases[{#}, (a:IdxPtn)/;!FreeQ[List@@a,IdxPtn], Infinity]}, 
		If[t =!= {}, Message[$PreRead::nestidx, t]]]&

$PreRead::wrongFree = "Free indices at `1` doesn't match in different terms."
$PreRead::wrongMulti = "Indices `1` appeared more than 2 times."
checkDummyIdx = Function[e, Module[{elist = ReleaseHold@plus2list@ReleaseHold@e, idStat, testFree, testMulti},
	idStat = Tally[idx@#]& /@ elist;
	testFree = DeleteDuplicates[Sort@Cases[#, {_, 1}] & /@ idStat];
	If[Length@testFree > 1, Message[$PreRead::wrongFree, testFree]];
	testMulti = Cases[idStat, {_, n_/;n>2}, Infinity];
	If[testMulti =!= {}, Message[$PreRead::wrongMulti, testMulti]];
]]

$PreRead := (Through@preCheckList@MakeExpression[#, StandardForm]; #)&

End[]
EndPackage[]