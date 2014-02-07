(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`decomp`", {"MathGR`tensor`", "MathGR`util`"}]

Decomp::usage = "Decomp[expr, rule, idx_:dummy] decomposes idx into parts. If idx not given, decompose all dummy indices"
Decomp0i::usage = "Decomp0i[expr, idx_:dummy] 1+d decomposition"
Decomp01i::usage = "Decomp01i[expr, idx_:dummy] 1+1+d decomposition"
Decomp1i::usage = "Decomp1i[expr, idx_:dummy] 1+d decomposition"
Decomp123::usage = "Decomp123[expr, idx_:dummy] 3-idx into 1+1+1"
Decomp0123::usage = "Decomp0123[expr, idx_:dummy] 4-idx into 1+1+1+1"
DecompSe::usage = "DecompSe[expr, idx_:dummy] N-idx into m+n in general"
DecompHook::usage = "Replacements after decomposition"

Begin["`Private`"]
Needs["MathGR`utilPrivate`"]

DeclareIdx[{UTot, DTot}, DimTot, LatinCapitalIdx, Blue]
DeclareIdx[{U1, D1}, Dim1, GreekIdx, Black]
DeclareIdx[{U2, D2}, Dim2, LatinIdx, Red]

If[!defQ@DecompHook,DecompHook = {}]
SetAttributes[{Decomp0i, Decomp01i, Decomp0123, Decomp}, HoldFirst]
Decomp[e_, decRule_, idList___]:= apply2term[decompTerm[#, decRule,
	Alternatives@@Cases[decRule[[1]], (tid_[_] -> _) :> tid, Infinity](* this is type of idx, like DTot|TTot *), idList]&, e]
decompTerm[t_, decRule_, idPtn_]:= Module[{totDummy}, 
	totDummy = Cases[Tally[ Cases[t, idPtn[a_]:>a,Infinity] ], {a_,2}:>a];
	decompTerm[t, decRule, idPtn, totDummy]]
decompTerm[t_, decRule_, idPtn_, idList_List]:= Module[{s=t, rule, id}, 
	Do[	rule = #[id]& /@ decRule; 
		If[(s/.rule[[1]])=!=s (* decompose only when idx exists *), 
			s = Total[s/.rule//.DecompHook]], {id, idList}]; 
	s//.DecompHook//Simp]

Decomp0i[e_, i___]:= Decomp[e, {{DTot@#->DE@0, UTot@#->UE@0}&, {DTot@#->DN@#, UTot@#->UP@#}&}, i]
Decomp01i[e_, i___]:= Decomp[e, {{DTot@#->DE@0, UTot@#->UE@0}&, {DTot@#->DE@1, UTot@#->UE@1}&, {DTot@#->DN@#, UTot@#->UP@#}&}, i]
Decomp0123[e_, i___]:= Decomp[e, {{DTot@#->DE@0, UTot@#->UE@0}&, {DTot@#->DE@1, UTot@#->UE@1}&, {DTot@#->DE@2, UTot@#->UE@2}&, {DTot@#->DE@3,UTot@#->UE@3}&}, i]
Decomp1i[e_, i___]:= Decomp[e, {{DTot@#->DE@1, UTot@#->UE@1}&, {DTot@#->DN@#, UTot@#->UP@#}&}, i]
Decomp123[e_, i___]:= Decomp[e, {{DTot@#->DE@1, UTot@#->UE@1}&, {DTot@#->DE@2, UTot@#->UE@2}&, {DTot@#->DE@3,UTot@#->UE@3}&}, i]
DecompSe[e_, i___] := Decomp[e, {{DTot@# -> D2@#, UTot@# -> U2@#}&, {DTot@# -> D1@#, UTot@# -> U1@#}&}, i]

End[]
EndPackage[]