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
AntiSym::usage = "AntiSym[expr, {a, b, ...}] anti-symmetrizes indices a, b, ... AntiSym[expr] anti-symmetrizes all free indices"

Dta::usage = "Delta symbol"
DtaGen::usage = "DtaGen[up..., dn...] is the generalized delta symbol"
Pd::usage = "Pd[f, DN@a] is partial derivative"
PdT::usage = "PdT[f, PdVars[DN@a, DN@b, ...]] is partial derivative"
PdVars::usage = "Pdvars[DN@a, DN@b, ...] is a list of derivative variables"
LeviCivita::usage = "LeviCivita[a, b, ...] is the Levi Civita tensor, defined only if dimension is given as an explicit number"

LatinIdx::usage = "strings {a, b, ..., }"
GreekIdx::usage = "strings {alpha, beta, ...}"
LatinCapitalIdx::usage = "strings {A, B, ...}"
UniqueIdx::usage = "unique vars {$n1, $n2, ...}"

DeclareSym::usage = "Declare tensor symmetry"
DeleteSym::usage = "DeleteSym[tensor, {UP, DN, ...}] deletes tensor symmetry"
Simp::usage = "Default simplification, with SimpHook applied"
SimpUq::usage = "Simp, keeping dummy unique"
SimpHook::usage = "Rules to apply before and after Simp"
SimpMSelect::usage = "A function to select terms to simplify, disregard others"

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
PdT[_Dta, PdVars[__]]:= 0

Options[DtaGen]={"DtaGenDta"->Dta}
DtaGen[ids:(_[_]..), OptionsPattern[]]:= Module[{btmp, tmp, i, d=Length[{ids}]/2, a, b},
	a = Take[{ids}, d]; b = Take[{ids}, -d]; 
	btmp = MapThread[#1[#2] &, {(b[[#]][[0]] & /@ Range[d]), tmp /@ Range[d]}];
	AntiSym[Product[OptionValue["DtaGenDta"][a[[i]], btmp[[i]]], {i, d}],btmp]/. (btmp[[#]]->b[[#]] &/@Range[d])]

DeclareIdx[ids_List, d_, set_List, color_]:= Module[{idsAlt=Alternatives@@ids}, PdT[d, PdVars[__]]:=0;
	Dim[idsAlt]:=d; IdxSet[idsAlt]:=set; IdxColor[idsAlt]:=color; add2set[IdxList, {ids}]; IdxPtn=Alternatives@@(Blank/@IdxList);
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

DeclareExplicitIdx[ids_List, color_]:= Module[{}, 
	(IdxColor[#]:=color; add2set[IdxNonSumList, #]; IdxNonSumPtn=Alternatives@@(Blank/@IdxNonSumList))&/@ids; IdxDual[ids[[1]]]=ids[[2]];IdxDual[ids[[2]]]=ids[[1]];
	Dta[(Alternatives@@ids)@i_, (Alternatives@@ids)@j_]:= KroneckerDelta[i, j]]

(*DeclareIdx[{UP, DN}, DefaultDim, GreekIdx, Black]*)
DeclareIdx[{UP, DN}, DefaultDim, LatinIdx, Black]

DeclareExplicitIdx[{UE, DE}, Gray]

idx:= Cases[times2prod@#,a:IdxPtn:>a[[1]],Infinity]& (* only find indices with Einstein convention *)
free:= Cases[Tally[idx@#], {a_,1}:>a] &
freeFull[e_]:= Cases[e, a:IdxPtn/;MemberQ[free@e, a[[1]]]:>a, Infinity]
dummy:= Cases[Tally[idx@#], {a_,2}:>a] &
getFreeSample:= free[getSampleTerm@#]&

Sym[e_, iList_]:= Plus@@ ( (e/.(iList~replaceTo~#)&) /@ Permutations[iList] )
AntiSym[e_, iList_]:= Plus@@ ( (Signature[#] e/.(iList~replaceTo~#)&) /@ Permutations[iList] )
Sym[e_]:= Sym[e, free@e]
AntiSym[e_]:= AntiSym[e, free@e]  

(* ::Section:: *)
(* Partial derivative *)

Pd[a_Plus, i_]:= Pd[#,i]& /@ a;
Pd[a_*b_, i_]:= Pd[a,i]*b + a*Pd[b,i];
Pd[f_^g_, i_]:= f^(g-1)*g*Pd[f,i] + f^g*Log[f]*Pd[g,i];
Pd[a_?NumericQ, i_]:=0;

SetAttributes[PdVars, Orderless]
PdT::nonpoly="Pd acting on non-polynomial objects (as `1`) is not supported."
PdT[f_, PdVars[]]:= f
PdT[a_?NumericQ, PdVars[__]]:=0;
PdT[f_/;MatchQ[Head[f],Plus|Times|Power], PdVars[i__]]:= Fold[Pd, f, {i}]
Pd[f_, i_]:= Piecewise[{{PdT[f, PdVars[i]], FreeQ[f, PdT]}, {PdT[f[[1]], PdVars[i, Sequence@@f[[2]]]], Head[f]==PdT}},
	Message[PdT::nonpoly, f];PdT[f, PdVars[i]]]

pd2pdts[expr_]:= expr /. PdT[f_, i_] :> If[FreeQ[f, IdxPtn|IdxNonSumPtn], pdts[Length@i][f][Sequence@@i], pdts[Length@i][Head@f][Sequence@@f, Sequence@@i]]
pdts2pd = #/. pdts[n_][f_][i__] :> If[n==Length@{i}, PdT[f, PdVars[i]], PdT[f@@Take[{i}, Length@{i} - n], PdVars@@Take[{i}, -n]]] &

(* ::Section:: *)
(* Simp functions *)

sumAlt:=Alternatives@@IdxList;

rmNE[e_] := DeleteCases[e, IdxNonSumPtn];

If[!defQ@simpMAss,simpMAss = True]
addAss[cond_]:= (simpMAss=Simplify[simpMAss&&cond];)

DeclareSym[t_,idx_,sym_]:= (If[sym===Symmetric[All]||sym==={Symmetric[All]}, SetAttributes[t, Orderless]];
	addAss[MAT[t][Sequence@@idx]~Element~Arrays[Dim/@rmNE[idx], sym]];)

DeleteSym[t_]:= DeleteSym[t,{___}]
DeleteSym[t_,idx_]:= Module[{del},
	del = Cases[{simpMAss}, Element[MAT[t][Sequence@@idx], _], Infinity];
	If[del==={}, Print["No match found in tensor definitions. Nothing is changed."];Return[]];
	Print["The following definitions has been deleted: ", del];
	ClearAttributes[t, Orderless];
	simpMAss = If[#==={}, True, Flatten[#][[1]]] &@ DeleteCases[{simpMAss}, Element[MAT[t][Sequence@@idx], _], Infinity];]

Simp::overdummy="Error: index `1` appears `2` times in `3`"
Simp::diffree="Error: free index `1` in term `2` is different from that of first term"
simpFterm[t_, fr1_]:= Module[{idStat, fr, dum, availDum, rule, a0},
       idStat = Tally[idx@t];
       If[Cases[idStat, {a_,b_}/;b>2]=!={}, Message[Simp::overdummy, Sequence@@(Cases[idStat, {a_,b_}/;b>2][[1]]), t]];
       fr = Sort@Cases[idStat, {a_,1}:>a];
       If[fr=!=fr1, Message[Simp::diffree, fr, t]];
       dum = Cases[idStat, {a_,2}:>a];
	availDum = Take[Complement[LatinIdx, fr], Length@dum];
	rule = replaceTo[(a0:sumAlt)/@dum, a0/@availDum];
	t /. rule]
simpF[e_]:= Module[{eList},
	eList = plus2list@e;
	Total[simpFterm[#, Sort@free@eList[[1]]]& /@ eList]]



Simp::ver="Warning: Mathematica version 8 or lower detected. Simp may not bring tensor to unique form"
simpH = If[$VersionNumber>8.99, simpM[simpF@#]&, Message[Simp::ver]; simpF]

If[!defQ@SimpHook,SimpHook = {}]

Options[Simp]= {"Method"->"Hybrid"}
Simp[e_, OptionsPattern[]]:= Switch[OptionValue["Method"], "Fast", simpF, "MOnly", simpM, _, simpH][e//.SimpHook]//.SimpHook//Expand
Options[SimpUq]= {"Method"->"Hybrid"}
SimpUq[e_, OptionsPattern[]]:= Block[{IdxSet}, (IdxSet[#]=IdxSet[IdxDual[#]]=UniqueIdx)&/@DeleteDuplicates[IdxList, IdxDual[#1] == #2 &]; Simp[e, "Method"->OptionValue["Method"]]]

(* ::Section:: *)
(* M-backend of Simp *)

simpMTermAss[tM_]:= Module[{tInPdts, ass=simpMAss, cnt},
	(* Add assumptions for tensors encountered in each term *)
	ass = ass && (And@@Cases[{tM},f:MAT[t_][idx__] 
		/;Cases[simpMAss, Element[f,__], Infinity]==={} (* This line is added to avoid duplicate assumptions, as a work around of a bug in M*)
		:>(f~Element~Arrays[Dim/@rmNE[{idx}]]), Infinity]);
	(* Add symmetry of T in PdPdPdT *)
	tInPdts = Cases[{tM}, HoldPattern[f:MAT[pdts[n_][t_]][idx__]] :>
		{MAT[t][Sequence@@Take[{idx},Length[{idx}]-n]],f,Dim/@rmNE[{idx}]}, Infinity];
	ass = ass && And@@Flatten[Cases[simpMAss,#[[1]]~Element~HoldPattern[Arrays[dim_,dom_,sym_]]:>
		#[[2]]~Element~Arrays[#[[3]],dom,sym],Infinity]&/@tInPdts];
	(* Add symmetry of PdPdPd in PdPdPdT *)
	ass = ass && And@@Flatten@Cases[{tM},f:MAT[pdts[n_][t_]][idx__] /; n>1 :> ((f~Element~Arrays[Dim/@rmNE[{idx}], Symmetric[#]])& 
		/@ (cnt=Length[{idx}]-n; Split[Cases[Take[{idx},-n],sumAlt],Function[{x,y},Dim[x]==Dim[y]]]/.{s:(sumAlt):> ++cnt})), Infinity] ]

Simp::ld="Warning: Memory constraint reached in `1`, simplification skipped"
tReduceMaxMemory=10^9 (* 1GB max memory *)
tReduce[e_]:= MemoryConstrained[TensorReduce[e], tReduceMaxMemory, Message[Simp::ld, term];e]

(* TODO: make this fix work faster, or use other method. *)
simpMTerm[fact_*term_, fr_, dum_, x_] /; FreeQ[fact, IdxPtn] := fact * simpMTerm[term, fr, dum, x];

Simp::nosupp="Warning: `1` has tensors in unsupported functions. This may cause mistake"
simpMTermSupported={prod}
simpMTermCheckSupported[e_]:= If[ (Flatten@{times2prod@e/.(# -> List & /@ simpMTermSupported)} // Cases[#, IdxPtn, {3, Infinity}] &) =!={}, Message[Simp::nosupp, e], "Supported"]
simpMTerm[term_, fr_, dum_, x_]:=Module[{t, tCt, tM, xFr, slots, tNewIdx, cnt, cntId, slot1, slot2, oldDummy=dummy@term},
	If[oldDummy==={}&&fr==={}, Return[term]]; (* no idx *)
	simpMTermCheckSupported[term];
	t = x ~TensorProduct~ times2prod[term, TensorProduct]; (* Add tensor product and contraction tensor *)
	tCt = Map[Flatten@Position[idx@t,#]&, fr~Join~oldDummy]; (* Determine contraction pairs *)
	tM = t /. id:IdxPtn:>id[[0]] /. f_[id__]:>MAT[f][id] /; !FreeQ[{id},sumAlt,1]; (* The tensor to input to TensorReduce *)
	(*Print[TensorContract1[tM, tCt]];Print[simpMTermAss[tM]];*)
	tM = times2prod[Assuming[simpMTermAss[tM], Expand@tReduce@TensorContract[tM, tCt]], List]; (* Outcome from TensorReduce *)
	(*Print[tM];*)
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

If[!defQ@SimpMSelect,SimpMSelect = Identity]
simpMHook:= {{(*here eval first*) plus2list, SimpMSelect, pd2pdts (*here eval last*)}, {pdts2pd, SimpMSelect,Total}}
simpM[e_]:= Module[{eList = Fold[#2[#1]&, e, simpMHook[[1]]](* apply init hook *), fr, dum, x},
	If[eList=={}, Return[0]]; (* SimpMSelect may return empty list *)
	fr = Sort@free@eList[[1]]; 
	x = If[fr==={}, 1, xMat@@(Function[i, Operate[IdxDual,i]]/@ SortBy[freeFull@eList[[1]], #[[1]]&]) ]; (* contraction tensor *) 
	(dum[#] = Complement[IdxSet[#], fr]) & /@ IdxList; (* Available free idx for each identifier *)
	Fold[#2[#1]&, simpMTerm[#,fr,dum,x]&/@eList, simpMHook[[2]]] (* Apply ending hook and return result *) ]


(* ::Section:: *)
(* Check tensor validity at $Pre *)

preCheckList = {checkNestIdx}

$PreRead::nestidx = "Nested indices are not allowed in `1`."
checkNestIdx = Module[{t=Cases[{#}, (a:IdxPtn)/;!FreeQ[List@@a,IdxPtn], Infinity]},
		If[t =!= {}, Message[$PreRead::nestidx, t]]]&

$PreRead := (Through@preCheckList@MakeExpression[#, StandardForm]; #)&

End[]
EndPackage[]