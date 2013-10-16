(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`ibp`", {"MathGR`tensor`"}]

TrySimp::usage = "TrySimp[expr, rule, rank] try to minimaize rank[expr] by applying rule"
Ibp::usage = "Ibp[expr, rank] do integration by parts and try to minimaize rank[expr]"
PdHold::usage = "Total derivative"
IbpCountLeaf::usage = "IbpCountPt2[e] counts leaves of e outside PdHold"
IbpCountPt2::usage = "IbpCountPt2[e] counts second time derivatives"
IbpCountPd2::usage = "IbpCountPd2[e] counts second derivatives"
IbpVar::usage = "IbpVar[var][e] counts Pd on specified var"
IbpStd2::usage = "Ibp count trying to bring second order Lagrangian to standard form"
IbpVariation::usage = "IbpVariation[e, var] is Ibp which eliminates derivative on var."

Begin["`Private`"]

trySimpStep[e_, rule_, rank_]:= Module[{ try = SortBy[{#, rank@#}& /@ ReplaceList[e, rule], Last] },
	If[try=!={} && try[[1,2]]<rank@e, PrintTemporary["Trying rules. Terms remaining: "<>ToString@Length@try[[1,1]]];try[[1,1]], e]]
TrySimp[e_, rule_, rank_:LeafCount, sel_:Identity]:= Module[{rest=#-sel[#]&}, FixedPoint[trySimpStep[sel@#, rule, rank]+rest@#&, Simp@e]] 

PdHold[0,_]:=0
PdHold /: -PdHold[a_,c_]:=PdHold[-a,c]
PdHold /: PdHold[a_,c_]+PdHold[b_,c_]:= PdHold[a+b,c]
PdHold[a_,id_[c_]]/;c!="(PdId)"&&!FreeQ[a,c]:=PdHold[a/.c:>"(PdId)",id@"(PdId)"]
Simp[b_.+PdHold[a_,c_]]:= Simp[b] + PdHold[Simp[a],c]

ibpRules = Dispatch@{ a_. b_^(n_.) Pd[b_,c_] + e_. :> PdHold[a b^(n+1) / (n+1), c] + e - Simp[ b^(n+1) Pd[a,c] / (n+1) ] /;n=!=-1,
	a_. Pd[Pd[b_,c_],d_] + e_. :> PdHold[a Pd[b,d], c] + e - Simp[Pd[b,d] Pd[a,c]],
	a_. Pd[b_,c_] + e_. :> PdHold[a b, c] + e - Simp[b Pd[a,c]],
	Pd[f_,a_]Pd[g_,b_]h_ + n_. :> PdHold[f Pd[g,b]h, a] - PdHold[f Pd[g,a]h, b] + Simp[Pd[f,b]Pd[g,a]h + f Pd[g,a]Pd[h,b] - f Pd[g,b] Pd[h,a]] + n,
	Pd[Pd[f_,a_],c_]Pd[g_,b_]h_ + n_. :> PdHold[Pd[f,c] Pd[g,b]h, a] - PdHold[Pd[f,c] Pd[g,a]h, b] + Simp[Pd[Pd[f,c],b]Pd[g,a]h + Pd[f,c] Pd[g,a]Pd[h,b] - Pd[f,c] Pd[g,b] Pd[h,a]] + n,
	Pd[Pd[f_,a_],c_]Pd[Pd[g_,b_],d_]h_ + n_. :> PdHold[Pd[f,c] Pd[Pd[g,d],b]h, a] - PdHold[Pd[f,c] Pd[Pd[g,d],a]h, b] + Simp[Pd[Pd[f,c],b]Pd[Pd[g,d],a]h + Pd[f,c] Pd[Pd[g,d],a]Pd[h,b] - Pd[f,c] Pd[Pd[g,d],b] Pd[h,a]] + n}

IbpCountLeaf[e_]:= LeafCount[e/._PdHold->0] * 10^-8
IbpCountPt2[e_]:= Count[{e/._PdHold->0}, Pd[Pd[a_, IdxNonSumPtn], IdxNonSumPtn], Infinity] + IbpCountLeaf[e]
IbpCountPd2[e_]:= Count[{e/._PdHold->0}, Pd[Pd[a_, _], _], Infinity] + IbpCountLeaf[e]
IbpVar[var_][e_]:= 10000*Count[{e/._PdHold->0}, Pd[Pd[Pd[a_/;!FreeQ[a, var], _],_],_], Infinity] + 100*Count[{e/._PdHold->0}, Pd[Pd[a_/;!FreeQ[a, var], _],_], Infinity] + Count[{e/._PdHold->0}, Pd[a_/;!FreeQ[a, var], _], Infinity] + IbpCountLeaf[e]
IbpStd2[e_]:= IbpCountPt2[e]*100 + Count[{e/._PdHold->0}, v_*Pd[v_,_]*_, Infinity] + IbpCountLeaf[e]

Ibp[e_, rank_:IbpCountLeaf, sel_:Identity]:= TrySimp[e, ibpRules, rank, sel]

IbpVariation[e_, v_]:=Expand[e] //. { a_.+b_.*Pd[f_,i_] /;FreeQ[b,v]&&!FreeQ[f,v] :> a-Expand[f*Pd[b,i]]} //Simp

End[]
EndPackage[]