(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`ibp`", {"MathGR`tensor`"}]

TrySimp::usage = "TrySimp[expr, rule, rank] try to minimaize rank[expr] by applying rule"
TrySimp2::usage = "TrySimp2[expr, rule, rank] try to minimaize rank[expr] by applying up to second order rules"
Ibp::usage = "Ibp[expr, rank] do integration by parts and try to minimaize rank[expr]"
Ibp2::usage = "Ibp[expr, rank] do integration by parts and try to minimaize rank[expr]. Second order rules are tried"
IbpRules::usage = "a list of rules to do ibp"
PdHold::usage = "Total derivative"
IdHold::usage = "Held identities"
IbpCountLeaf::usage = "IbpCountPt2[e] counts leaves of e outside PdHold"
IbpCountPt2::usage = "IbpCountPt2[e] counts second time derivatives"
IbpCountPd2::usage = "IbpCountPd2[e] counts second derivatives"
IbpVar::usage = "IbpVar[var][e] counts Pd on specified var"
IbpStd2::usage = "Ibp count trying to bring second order Lagrangian to standard form"
IbpVariation::usage = "IbpVariation[e, var] is Ibp which eliminates derivative on var."
IbpReduceVars::usage = "IbpReduceVars[vars_List][e] counts power of vars."

Begin["`Private`"]
Needs["MathGR`utilPrivate`"]

trySimpStep[e_, rule_, rank_, level_:1]:= Module[{ try, replaceFun },
	replaceFun = Function[list, Flatten@Map[ReplaceList[#, rule] &, list]];
	try = SortBy[{#, rank@#}& /@ Nest[replaceFun, {e}, level], Last];
	If[try=!={} && try[[1,2]]<rank@e, PrintTemporary["Trying rules. Terms remaining: "<>ToString@Length@try[[1,1]]];try[[1,1]], e]]
TrySimp[e_, rule_, rank_:LeafCount, sel_:Identity]:= Module[{rest=#-sel[#]&}, FixedPoint[trySimpStep[sel@#, rule, rank]+rest@#&, Simp@e]] 

TrySimp2[e_, rule_, rank_:LeafCount]:= Module[{resStage, res2},
	resStage = TrySimp[e, rule, rank];
	PrintTemporary["Trying more rules, please wait..."];
	res2 = trySimpStep[e, rule, rank, 2];
	TrySimp[res2, rule, rank]]

PdHold[0,_]:=0
PdHold /: -PdHold[a_,c_]:=PdHold[-a,c]
PdHold /: n_?NumericQ PdHold[a_,c_]:=PdHold[n a,c]
PdHold /: PdHold[a_,c_]+PdHold[b_,c_]:= PdHold[a+b,c]
PdHold[a_,id_[c_]]/;c!="(PdId)"&&!FreeQ[a,c]&&id=!=DE:=PdHold[a/.c:>"(PdId)",id@"(PdId)"]
Simp[b_.+PdHold[a_,c_]]:= Simp[b] + PdHold[Simp[a],c]

Simp[b_.+IdHold[a_]]:= Simp[b] + IdHold[Simp[a]]

IbpRules = Dispatch@{ a_. b_^(n_.) Pd[b_,c_] + e_. :> PdHold[a b^(n+1) / (n+1), c] + e - Simp[ b^(n+1) Pd[a,c] / (n+1) ] /;n=!=-1,
	a_. Pd[Pd[b_,c_],d_] + e_. :> PdHold[a Pd[b,d], c] + e - Simp[Pd[b,d] Pd[a,c]],
	a_. Pd[b_,c_]^n_ + e_. :> PdHold[a b Pd[b, c]^(n-1), c] - Simp[b Pd[a Pd[b, c]^(n-1), c]] + e /;n>0&&Element[n,Integers],
	a_. Pd[b_,c_] + e_. :> PdHold[a b, c] + e - Simp[b Pd[a,c]],
	Pd[f_,a_]Pd[g_,b_]h_ + n_. :> PdHold[f Pd[g,b]h, a] - PdHold[f Pd[g,a]h, b] + Simp[Pd[f,b]Pd[g,a]h + f Pd[g,a]Pd[h,b] - f Pd[g,b] Pd[h,a]] + n,
	Pd[Pd[f_,a_],c_]Pd[g_,b_]h_ + n_. :> PdHold[Pd[f,c] Pd[g,b]h, a] - PdHold[Pd[f,c] Pd[g,a]h, b] + Simp[Pd[Pd[f,c],b]Pd[g,a]h + Pd[f,c] Pd[g,a]Pd[h,b] - Pd[f,c] Pd[g,b] Pd[h,a]] + n,
	Pd[Pd[f_,a_],c_]Pd[Pd[g_,b_],d_]h_ + n_. :> PdHold[Pd[f,c] Pd[Pd[g,d],b]h, a] - PdHold[Pd[f,c] Pd[Pd[g,d],a]h, b] + Simp[Pd[Pd[f,c],b]Pd[Pd[g,d],a]h + Pd[f,c] Pd[Pd[g,d],a]Pd[h,b] - Pd[f,c] Pd[Pd[g,d],b] Pd[h,a]] + n,
	(* expansion of Pd[f Pd[g,a]^2 Pd[Pd[g,b],b], c] *)
	e_. + f_. Pd[Pd[g_, a_], a_] Pd[Pd[g_, b_], b_] Pd[g_, c_] :> e - PdHold[f Pd[g, a]^2 Pd[Pd[g, b], b], c]/2 + PdHold[f Pd[g, c] Pd[g, a] Pd[Pd[g, b], b], a] + PdHold[f Pd[g, a]^2 Pd[Pd[g, b], c], b]/2 - PdHold[Pd[f Pd[g, a]^2, b] Pd[g, c], b]/2 
		+ Simp[Pd[f, c] Pd[g, a]^2 Pd[Pd[g, b], b]/2 - Pd[g, c] Pd[f, a] Pd[g, a] Pd[Pd[g, b], b] + Pd[g, c] Pd[Pd[f, b], b] Pd[g, a]^2/2 + 2 Pd[f, b] Pd[Pd[g, a], b] Pd[g, a] Pd[g, c] + f Pd[Pd[g, a], b]^2 Pd[g, c]],
	(* expansion of PdHold[Pd[z, a] Pd[z, b] Pd[Pd[c, b], a], at] *)
	x_. + y_.*Pd[z_, a_] Pd[Pd[z_, at_], b_] Pd[Pd[c_, a_], b_] :> x + PdHold[y Pd[z, a] Pd[z, b] Pd[Pd[c, b], a], at]/2 - Simp[Pd[z, a] Pd[z, b] Pd[y Pd[Pd[c, b], a], at]/2]
}

holdPtn=_PdHold|_IdHold
IbpCountLeaf[e_]:= LeafCount[e/.holdPtn->0] * 10^-5
IbpCountPt2[e_]:= Count[{e/.holdPtn->0}, Pd[Pd[a_, IdxNonSumPtn], IdxNonSumPtn], Infinity] + IbpCountLeaf[e]
IbpCountPd2[e_]:= Count[{e/.holdPtn->0}, Pd[Pd[a_, _], _], Infinity] + IbpCountLeaf[e]
IbpVar[var_][e_]:= 10000*Count[{e/.holdPtn->0}, Pd[Pd[Pd[a_/;!FreeQ[a, var], _],_],_], Infinity] + 100*Count[{e/.holdPtn->0}, Pd[Pd[a_/;!FreeQ[a, var], _],_], Infinity] + Count[{e/.holdPtn->0}, Pd[a_/;!FreeQ[a, var], _], Infinity] + IbpCountLeaf[e]
IbpStd2[e_]:= IbpCountPt2[e]*100 + Count[{e/.holdPtn->0}, v_*Pd[v_,_]*_, Infinity] + IbpCountLeaf[e]

IbpReduceVars[vars_List][e_]:=Module[{eOrderList, tmp},
	eOrderList = Count[{#}, Alternatives@@vars, Infinity] & /@ times2prod@plus2list[e+tmp /.holdPtn->0];
	Total[100^(5-#)&/@eOrderList]-100^5 + IbpCountLeaf[e]]

Ibp[e_, rank_:IbpCountLeaf, sel_:Identity]:= TrySimp[e, IbpRules, rank, sel]
Ibp2[e_, rank_:IbpCountLeaf]:= TrySimp2[e, IbpRules, rank]

IbpVariation[e_, v_]:=Expand[e] //. { a_.+b_.*Pd[f_,i_] /;FreeQ[b,v]&&!FreeQ[f,v] :> a-Expand[f*Pd[b,i]]} //Simp

End[]
EndPackage[]