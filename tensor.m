(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`tensor`"]

DeclareIdx::usage = "DeclareIdx[ids_List, dim, set, color] defines dim, which set of idx to use and color for a pair of indices (upper, lower)"
DeclareExplicitIdx::usage = "DeclareExplicitIdx[ids_List, color] defines a pair of explicit index and display color"
IdxList::usage = "list of idx headers, e.g. {UP, DN}"
IdxPtn::usage = "pattern of idx, e.g. _DN|_UP"
IdxHeadPtn::usage = "Pattern of head of idx, e.g. DN|UP"
IdxUpList::usage = "A list of upper index identifiers"
IdxUpPtn::usage = "A pattern object to label upper index identifiers"
IdxDnList::usage = "A list of lower index identifiers"
IdxDnPtn::usage = "A pattern object to label lower index identifiers"
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
AntiSym::usage = "AntiSym[expr, {a, b, ...}] anti-symmetrizes indices a, b, ... AntiSym[expr] anti-symmetrizes all free indices"

Dta::usage = "Delta symbol"
DtaGen::usage = "DtaGen[up..., dn...] is the generalized delta symbol"
Pd::usage = "Pd[f, DN@a] is partial derivative"
PdT::usage = "PdT[f, PdVars[DN@a, DN@b, ...]] is partial derivative"
PdVars::usage = "Pdvars[DN@a, DN@b, ...] is a list of derivative variables"
Pm2::usage = "Pm2[expr] is \\partial^{-2} expr. This inversed Laplacian should be understood in momentum space"
LeviCivita::usage = "LeviCivita[a, b, ...] is the Levi Civita tensor, defined only if dimension is given as an explicit number"

LatinIdx::usage = "strings {a, b, ..., }"
GreekIdx::usage = "strings {alpha, beta, ...}"
LatinCapitalIdx::usage = "strings {A, B, ...}"
UniqueIdx::usage = "unique vars {$n1, $n2, ...}"

DeclareSym::usage = "Declare tensor symmetry"
DeleteSym::usage = "DeleteSym[tensor, {UP, DN, ...}] deletes tensor symmetry"
Simp::usage = "Simplification, which brings tensors into canonical form. Simp is default to SeriSimp"
SimpHook::usage = "Rules to apply before and after Simp"
SimpSelect::usage = "A function to select terms to simplify, disregard others"
ParaSimp::usage = "ParaSimp[expr] simplifies expr in parallel"
SeriSimp::usage = "ParaSimp[expr] simplifies expr in parallel"
SimpUq::usage = "SimpUq is identical to Simp[#, \"Dummy\"->\"Unique\"]&"

\[Bullet]::usage = "Symbol for time derivative"
\[CapitalSampi]::usage = "Symbol for general derivative"

Begin["`Private`"]
Needs["MathGR`utilPrivate`"]

Uq[n_Integer]:= Sequence@@Table[Unique[],{n}]
Uq[100]; (* Very strange that the first 100 unique variables are much slower to use in some options (that Simp used). *)

(* ::Section:: *)
(* Idx utilities *)

LatinIdx = Join[FromCharacterCode /@ Range[97, 97 + 24], "y"<>ToString[#]&/@Range[26]]
GreekIdx = Join[FromCharacterCode /@ Range[945, 945 + 24], "\[Omega]"<>ToString[#]&/@Range[26]]
LatinCapitalIdx = Join[FromCharacterCode /@ Range[65, 65 + 24], "Y"<>ToString[#]&/@Range[26]]
UniqueIdx:= Unique[]& /@ Range[50]

SetAttributes[Dta, Orderless]
PdT[_Dta, PdVars[__]]:= 0

Options[DtaGen]={"DtaGenDta"->Dta}
DtaGen[ids:(_[_]..), OptionsPattern[]]:= Module[{btmp, tmp, i, d=Length[{ids}]/2, a, b},
	a = Take[{ids}, d]; b = Take[{ids}, -d]; 
	btmp = MapThread[#1[#2] &, {(b[[#]][[0]] & /@ Range[d]), tmp /@ Range[d]}];
	AntiSym[Product[OptionValue["DtaGenDta"][a[[i]], btmp[[i]]], {i, d}],btmp]/. (btmp[[#]]->b[[#]] &/@Range[d])]

DeclareIdx[ids_List, d_, set_List, color_]:= Module[{idsAlt=Alternatives@@ids}, PdT[d, PdVars[__]]:=0;
	Dim[idsAlt]:=d; IdxSet[idsAlt]:=set; IdxColor[idsAlt]:=color; add2set[IdxList, {ids}]; IdxHeadPtn=Alternatives@@IdxList; IdxPtn=Alternatives@@(Blank/@IdxList);
	IdxDual[ids[[1]]]=ids[[2]];	IdxDual[ids[[2]]]=ids[[1]];
	idxIdentity[ids[[1]]] = idxIdentity[ids[[2]]] = Unique[];
	add2set[IdxUpList,ids[[1]]]; IdxUpPtn=Alternatives@@(Blank/@IdxUpList);
	add2set[IdxDnList,ids[[2]]]; IdxDnPtn=Alternatives@@(Blank/@IdxDnList);
	Dta[idsAlt@a_, idsAlt@a_]:= d;
	Dta/:Power[Dta[idsAlt@a_, idsAlt@b_], 2]:= d;
	Dta/:HoldPattern[Times][f__, Dta[(a:idsAlt)@m_, (b:idsAlt)@n_]] /; !FreeQ[Hold[f], (ids[[1]][n])|(ids[[2]][n])|(ids[[1]][m])|(ids[[2]][m])]
		:= Piecewise[{{Times[f]/.(c:idsAlt)@n -> c@m, !FreeQ[Hold[f], (ids[[1]][n])|(ids[[2]][n])]}, 
		{Times[f]/.(c:idsAlt)@m -> c@n, !FreeQ[Hold[f], (ids[[1]][m])|(ids[[2]][m])]}},	Times[f, Dta[a@m, b@n]]];
	If[IntegerQ[d],
		DeclareSym[LeviCivita, ConstantArray[#, d], Antisymmetric[All]]& /@ ids;
		LeviCivita /: LeviCivita[a:(ids[[1]][_]..)]*LeviCivita[b:(ids[[2]][_]..)]:= DtaGen[a,b];  ]]

DeclareIdx[{UP, DN}, DefaultDim, LatinIdx, Black]

IdxColor[UE|DE]=Gray;
Dta[(UE|DE)@i_, (UE|DE)@j_]:= KroneckerDelta[i, j]
rmE = DeleteCases[#, _UE|_DE]&

idx:= Cases[times2prod@#,a:IdxPtn:>a[[1]],Infinity]& (* only find indices with Einstein convention *)
free:= Cases[Tally[idx@#], {a_,1}:>a] &
dummy:= Cases[Tally[idx@#], {a_,2}:>a] &
getFreeSample:= free[getSampleTerm@#]&

Sym[e_, iList_]:= Plus@@ ( (e/.(iList~replaceTo~#)&) /@ Permutations[iList] )
AntiSym[e_, iList_]:= Plus@@ ( (Signature[#] e/.(iList~replaceTo~#)&) /@ Permutations[iList] )
Sym[e_]:= Sym[e, free@e]
AntiSym[e_]:= AntiSym[e, free@e]  

(* ::Section:: *)
(* Partial derivative *)

Pd[a_Plus, i_]:= Pd[#,i]& /@ a
Pd[a_*b_, i_]:= Pd[a,i]*b + a*Pd[b,i]
Pd[f_^g_, i_]:= f^(g-1)*g*Pd[f,i] + f^g*Log[f]*Pd[g,i]
Pd[a_?NumericQ, i_]:=0

Pd[f_, i_]:= Piecewise[{
	    {PdT[f, PdVars[i]], FreeQ[f, PdT]}, 
		{PdT[f[[1]], PdVars[i, Sequence@@f[[2]]]], Head[f]===PdT},
		{Pm2[Pd[f[[1]], i], f[[2]]], Head[f]===Pm2} },
	Message[PdT::nonpoly, f];PdT[f, PdVars[i]]]

SetAttributes[PdVars, Orderless]
PdT::nonpoly="Pd acting on non-polynomial objects (as `1`) is not supported."
PdT[f_, PdVars[]]:= f
PdT[a_?NumericQ, PdVars[__]]:=0
PdT[f_/;MatchQ[Head[f],Plus|Times|Power|Pd|PdT], PdVars[i__]]:= Fold[Pd, f, {i}]

pd2pdts[expr_]:= expr /. PdT[f_, i_] :> If[FreeQ[f, IdxPtn|_UE|_DE], pdts[Length@i][f][Sequence@@i], pdts[Length@i][Head@f][Sequence@@f, Sequence@@i]]
pdts2pd = #/. pdts[n_][f_][i__] :> If[n==Length@{i}, PdT[f, PdVars[i]], PdT[f@@Take[{i}, Length@{i} - n], PdVars@@Take[{i}, -n]]] &

Pm2[f_. Power[a_Plus, n_.], type_] /; IntegerQ[n]&&0<=n<5 := Pm2[f #, type]& /@ Expand[a^n]
Pm2[f_*g_, type_] /; Pd[f, type@testVar]===0 := f Pm2[g, type]
Pm2[PdT[f_, PdVars[i__]], type_]:= PdT[Pm2[f, type], PdVars[i]]
PdT[Pm2[f_, type_], PdVars[type_@i_, type_@i_, etc___]]:= PdT[f, PdVars[etc]]

(* ::Section:: *)
(* Declare and delete symmetries *)

If[!defQ@simpMAss,simpMAss = True]
addAss[cond_]:= (simpMAss=Simplify[simpMAss&&cond];)

DeclareSym[t_,id_,sym_]:= (If[sym===Symmetric[All]||sym==={Symmetric[All]}, SetAttributes[t, Orderless]];
	addAss[MAT[t][Sequence@@id]~Element~Arrays[Dim/@rmE[id], sym]];)

DeleteSym[t_]:= DeleteSym[t,{___}]
DeleteSym[t_,id_]:= Module[{del},
	del = Cases[{simpMAss}, Element[MAT[t][Sequence@@id], _], Infinity];
	If[del==={}, Print["No match found in tensor definitions. Nothing is changed."];Return[]];
	Print["The following definitions has been deleted: ", del];
	ClearAttributes[t, Orderless];
	simpMAss = If[#==={}, True, Flatten[#][[1]]] &@ DeleteCases[{simpMAss}, Element[MAT[t][Sequence@@id], _], Infinity];]

(* ::Section:: *)
(* Simp functions *)

Simp::overdummy = "Error: index `1` appears `2` times in `3`"
Simp::diffree = "Error: free index in term `1` is different from that of first term (`2`)"
Simp::ld = "Warning: Memory constraint reached in `1`, simplification skipped"
If[!defQ@Simp, Simp:= SeriSimp]
SimpUq:= Simp[#, "Dummy"->"Unique"]&

tReduceMaxMemory=10^9 (* 1GB max memory *)
tReduce[e_]:= MemoryConstrained[TensorReduce[e], tReduceMaxMemory, Message[Simp::ld, term];e]
If[!defQ@SimpSelect, SimpSelect = Identity]
If[!defQ@SimpHook, SimpHook = {}]
Options[SeriSimp]= {"Method"->"Hybrid" (* Fast for simple pass only, M for M pass only *), "Dummy"->"Friendly" (* or Unique *)}
SeriSimp[e_, OptionsPattern[]]:= Module[{eList, fr, simpTermFast, idStat, frTerm, dum, conTsr, zMat, simpTerm, tM, idSet, dumSet},
	eList = SimpSelect @ plus2list @ (e//.SimpHook);
	If[eList==={} || eList==={0}, Return @ 0];
	fr = Sort @ free @ eList[[1]];
	
	(* 1st pass, check tensor and replace dummy, try to cancel some terms *)
	simpTermFast[t_]/; FreeQ[t, IdxPtn]:=t;	
	simpTermFast[t_]:= ( idStat=Tally@idx@t;
		frTerm = Sort@Cases[idStat, {a_,1}:>a];
		If[Cases[idStat, {a_,b_}/;b>2]=!={}, Message[Simp::overdummy, Sequence@@(Cases[idStat, {a_,b_}/;b>2][[1]]), t]];
		If[frTerm=!=fr, Message[Simp::diffree, t, fr]];
		dum = Cases[idStat, {a_,2}:>a];
		t /. replaceTo[(a0:IdxHeadPtn) /@ dum, a0 /@ Take[Complement[LatinIdx, frTerm], Length@dum]] );
	If[OptionValue@"Method"=!="M", eList = plus2listRaw @ Total @ Map[simpTermFast, eList]];
	If[OptionValue@"Method"==="Fast", Return @ Total @ eList];

	(* 2nd pass, with M engine *)
	conTsr = If[fr==={}, 1, zMat @@ SortBy[Cases[eList[[1]], (i:IdxHeadPtn)[a_]/;MemberQ[fr, a], Infinity], First]];
	simpTerm[f_]/; !FreeQ[f, Pm2]:=f; (* Full simp of Pm2 not supported, due to limited need *)	
	simpTerm[f_]/; FreeQ[f, IdxPtn]:=f;	
	simpTerm[f_ t_] /; FreeQ[f, IdxPtn]:=f * simpTerm[t];
	simpTerm[term_]:= ( t = conTsr~TensorProduct~times2prod[term, TensorProduct];
		tM = TensorContract[t /. id:IdxPtn:>id[[0]] /. f_[id__]:>MAT[f][id] /; !FreeQ[{id},IdxHeadPtn,1], Map[Flatten@Position[idx@t,#]&, dummy@t]];
		Assuming[simpTermAss@tM[[1]], tReduce@tM] );
	eList = plus2listRaw @ Total @ Map[simpTerm, pd2pdts @ eList];

	(* 3rd pass, get indices back *)
	idSet = If[OptionValue@"Dummy"==="Unique", UniqueIdx, IdxSet[#]]&;
	(dumSet[#] = Complement[idSet[#], fr]) & /@ IdxList;
	eList = assignIdx[#, fr, dumSet, conTsr, zMat]& /@ eList;
	(Total @ SimpSelect @ pdts2pd @ eList)//.SimpHook]


assignIdx[tM_, fr_, dumSet_, conTsr_, zMat_]/; !FreeQ[tM, Pm2]:= tM; (* Full simp of Pm2 not supported, due to limited need *)
assignIdx[tM_, fr_, dumSet_, conTsr_, zMat_]/; FreeQ[tM, IdxHeadPtn]:= tM;
assignIdx[f_ tM_, fr_, dumSet_, conTsr_, zMat_]/; FreeQ[f, IdxHeadPtn]:= f assignIdx[tM, fr, dumSet, conTsr, zMat];
assignIdx[tM_, fr_, dumSet_, conTsr_, zMat_]:= Module[{tcGetId, nthCT=0, nthIdx (* used by restoreContract, count idx number within a TensorContract *), 
		mark (* mark idx with mark[nthCT, nthIdX] *), nthDummy (* used by assignDummy, count which dummy variable to use from dumSet *), marked, assignFree, assignDummy}, 
	tcGetId[t_, pairs_]:= (nthIdx=1; nthCT++; t /. a:IdxHeadPtn:>a[mark[nthCT, nthIdx++]] /. (mark[nthCT, #[[2]]]->mark[nthCT, #[[1]]] &/@ pairs));
	assignFree[x_]:= x /. Flatten@Cases[{x}, MAT[zMat][a__] :> replaceTo[#[[1]]&/@{a}, fr], Infinity]; (* put free indices *)
	(nthDummy[#]=1)& /@ IdxList; (* Initialize counter for assignDummy -- each type is initially 1 *)
	assignDummy[x_]:= x /. (marked = DeleteDuplicates[#, First[#1] === First[#2] &]& @ Cases[x, _@mark[__], Infinity]; (* find dummy indices, one representive for each pair *)
		replaceTo[First/@marked, dumSet[#[[0]]][[(nthDummy[#[[0]]])++;(nthDummy@IdxDual[#[[0]]])++]] & /@ marked]); (* replace those marked indices with standard dummies *)
	assignDummy @ assignFree @ (times2prod[tM, TensorProduct]/.TensorContract->tcGetId) /. MAT[f_]:>f /. zMat[i__]:>1 // prod2times[#, TensorProduct]&]

simpTermAss[tM_]:= Module[{tInPdts, ass=simpMAss, cnt},
	(* Add assumptions for tensors encountered in each term *)
	ass = ass && (And@@Cases[{tM},f:MAT[t_][idx__] 
		/;Cases[simpMAss, Element[f,__], Infinity]==={} (* This line is added to avoid duplicate assumptions, as a work around of a bug in M*)
		:>(f~Element~Arrays[Dim/@rmE[{idx}]]), Infinity]);
	(* Add symmetry of T in PdPdPdT *)
	tInPdts = Cases[{tM}, HoldPattern[f:MAT[pdts[n_][t_]][idx__]] :> {MAT[t][Sequence@@Take[{idx},Length[{idx}]-n]],f,Dim/@rmE[{idx}]}, Infinity];
	ass = ass && And@@Flatten[Cases[simpMAss,#[[1]]~Element~HoldPattern[Arrays[dim_,dom_,sym_]]:> #[[2]]~Element~Arrays[#[[3]],dom,sym],Infinity]&/@tInPdts];
	(* Add symmetry of PdPdPd in PdPdPdT *)
	ass = ass && And@@Flatten@Cases[{tM},f:MAT[pdts[n_][t_]][idx__] /; n>1 :> ((f~Element~Arrays[Dim/@rmE[{idx}], Symmetric[#]])& 
		/@ (cnt=Length[{idx}]-n; Split[Cases[Take[{idx},-n],sumAlt],Function[{x,y},Dim[x]==Dim[y]]]/.{s:(sumAlt):> ++cnt})), Infinity] ]

Options[ParaSimp] = {"N" -> $ConfiguredKernels[[1, 1]], "Simp" :> (Expand[SeriSimp[#, "Method"->"M"] //. SimpHook] &)};
ParaSimp[e_, OptionsPattern[]] := Module[{eList = plus2listRaw[e //. SimpHook // SeriSimp[#, "Method"->"Fast"]&], func = OptionValue["Simp"], parts, subLen},
  subLen = Ceiling[Length@eList/OptionValue["N"]];
  parts = Partition[eList, subLen, subLen, 1, 0];
  Total @ ParallelMap[func @ Total @ # &, parts, DistributedContexts -> "MathGR`"]]


(* ::Section:: *)
(* Check tensor validity at $Pre *)

preCheckList = {checkNestIdx}

$PreRead::nestidx = "Nested indices are not allowed in `1`."
checkNestIdx = Module[{t=Cases[{#}, (a:IdxPtn|_UE|_DE)/;!FreeQ[List@@a,IdxPtn|_UE|_DE], Infinity]},
		If[t =!= {}, Message[$PreRead::nestidx, t]]]&

$PreRead := (Through@preCheckList@MakeExpression[#, StandardForm]; #)&

End[]
EndPackage[]