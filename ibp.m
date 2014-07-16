(* ::Package:: *)

(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`ibp`", {"MathGR`tensor`"}]

TrySimp::usage = "TrySimp[expr, rule, rank] try to minimaize rank[expr] by applying rule"
TrySimp2::usage = "TrySimp2[expr, rule, rank] try to minimaize rank[expr] by applying up to second order rules"
Ibp::usage = "Ibp[expr, rank] do integration by parts and try to minimaize rank[expr]"
IbpNB::usage = "IbpNB[f__] is Ibp, with boundary term set to zero"
Pm2Rules::usage = "Rules to simplify Pm2 expressions"
Pm2Simp::usage = "Simplify Pm2 using Pm2Rules"
Ibp2::usage = "Ibp[expr, rank] do integration by parts and try to minimaize rank[expr]. Second order rules are tried"
IbpRules::usage = "a list of rules to do ibp"
PdHold::usage = "Total derivative"
IdHold::usage = "Held identities"
IbpCountLeaf::usage = "IbpCountLeaf[e] counts leaves of e outside PdHold or IdHold"
IbpCountTerm::usage = "IbpCountTerm[e] counts terms of e outside PdHold or IdHold"
IbpCountPt2::usage = "IbpCountPt2[e] counts second time derivatives"
IbpCountPd2::usage = "IbpCountPd2[e] counts second derivatives"
IbpVar::usage = "IbpVar[var][e] counts Pd on specified var"
IbpStd2::usage = "Ibp count trying to bring second order Lagrangian to standard form"
IbpVariation::usage = "IbpVariation[e, var] is Ibp which eliminates derivative on var."
IbpReduceOrder::usage = "IbpReduceOrder[vars_List][e] counts power of vars."
TrySimpPreferredPattern::usage = "a pattern which Ibp tries to keep"
TrySimpPreferredPatternStrength::usage = "How strongly TrySimpPreferredPattern is preferred"
Begin["`Private`"]
Needs["MathGR`utilPrivate`"]

try[rule_, rank_, 0][e_]:= e
try[rule_, rank_, level_][e_] /;IntegerQ[level]&&level>0 := FixedPoint[tryStep[rule, rank, level], e]

tryStepCropList = take[#, 100]&
(*tryStepCropList = Take[#, IntegerPart[Length@#/3.0]+1] &*)
(*tryStepCropList = Identity*)

tryStep[rule_, rankRaw_, level_][eRaw_]:= Module[{e, trials, tryRulesOnList, sortByRank, replaceListOnList = Map[ReplaceList[#, rule]&, #]&, rank},
	e = try[rule, rank, level-1] @ eRaw;
  rank = TrySimpRank@rankRaw;
  sortByRank=SortBy[#, rank]&;
	tryRulesOnList = tryStepCropList @ sortByRank @ DeleteDuplicates @ Flatten @ replaceListOnList @ # &;
	trials = Nest[tryRulesOnList, {e}, level];
	If[trials=!={} && rank@trials[[1]]<rank@e, 
		PrintTemporary["Improved at level "<>ToString[level]<>", with rank "<>ToString@CForm@N@rank@trials[[1]] ]; trials[[1]], 
		PrintTemporary["No improvement found at level "<>ToString[level]<>". Try harder or stop."];e] ]

Options[TrySimp] = {"Rank"->LeafCount, "Level"->1}
TrySimp[e_, rule_, OptionsPattern[]]:= try[rule, OptionValue@"Rank", OptionValue["Level"]][e]

Pm2Simp[e_]:= TrySimp[Simp@e, Pm2Rules, "Rank"->IbpCountLeaf]

If[!defQ@TrySimpPreferredPattern, TrySimpPreferredPattern={}];
If[!defQ@TrySimpPreferredPatternStrength, TrySimpPreferredPatternStrength=10^-4];
TrySimpRank[rankf_][e_]:= rankf[e] - TrySimpPreferredPatternStrength Count[{e/.holdPtn->0}, TrySimpPreferredPattern, Infinity];


(* ::Section:: *)
(* Below are IBP rules and rank functions *)


PdHold[0,_]:=0
PdHold /: -PdHold[a_,c_]:=PdHold[-a,c]
PdHold /: n_?NumericQ PdHold[a_,c_]:=PdHold[n a,c]
PdHold /: PdHold[a_,c_]+PdHold[b_,c_]:= PdHold[a+b,c]
PdHold[a_,id_[c_]]/;c!="(PdId)"&&!FreeQ[a,c]&&id=!=DE:=PdHold[a/.c:>"(PdId)",id@"(PdId)"]

Simp[b_. + f_. PdHold[a_,c_], opt:OptionsPattern[]]:= Simp[b, opt] + Simp[f, opt] PdHold[Simp[a, opt],c]
Simp[b_. + f_. IdHold[a_], opt:OptionsPattern[]]:= Simp[b, opt] + Simp[f, opt] IdHold[Simp[a, opt]]

Pm2Rules = Dispatch@{(* Note: Pm2 is defined in momentum space. Thus there is no well-defined boundary term *)
	x_. + a_ Pm2[b_, type_] /; Pd[a, type@testVar]=!=0 :> x + Simp[Pm2[a, type] b],
	x_. + a_ PdT[Pm2[b_, type_], PdVars[e__]] /; Pd[a, type@testVar]=!=0 :> x + Simp[Pm2[a, type] PdT[b, PdVars[e]]],
	x_. + a_. Pm2[ g_ PdT[f_, PdVars[type_@i_, type_@i_, e___]] , type_] :> 
		x + Simp[ a (PdT[f, PdVars[e]] g - 2 Pm2[PdT[f, PdVars[type@i, e]] Pd[g, type@i], type] - Pm2[PdT[f, PdVars[e]] Pd[Pd[g, type@i], type@i], type]) ],
	x_. + b_. Pm2 [a_. f_ PdT[f_, PdVars[type_@i_, type_@i_]] , type_] :> 
		x + Simp[ (b/2) ( a f^2  - Pm2[ Pd[Pd[a, type@i], type@i] f^2 + 4 Pd[a, type@i] f Pd[f, type@i] + 2 a Pd[f, type@i]^2 , type] ) ],
	x_. + b_. Pm2 [a_. PdT[h_, PdVars[e___]] PdT[h_, PdVars[type_@i_, type_@i_, e___]] , type_] :> With[{f = PdT[h, PdVars[e]]},
		x + Simp[ (b/2) ( a f^2  - Pm2[ Pd[Pd[a, type@i], type@i] f^2 + 4 Pd[a, type@i] f Pd[f, type@i] + 2 a Pd[f, type@i]^2 , type] ) ]]}

IbpRules = Dispatch@({
	(*a_. PdT[b_, PdVars[c_, etc___]] + e_. :> PdHold[a PdT[b, PdVars[etc]], c] + e - Simp[PdT[b, PdVars[etc]] Pd[a,c]],*)
	a_. PdT[b_, PdVars[c_, etc___]]^n_. + e_. :> Simp[PdHold[a PdT[b, PdVars[etc]] PdT[b, PdVars[c, etc]]^(n-1), c] - PdT[b, PdVars[etc]] Pd[a PdT[b, PdVars[c, etc]]^(n-1), c]] + e,
  a_. PdT[b_, PdVars[c_, d_, etc___]] + e_. :> Simp[PdHold[a PdT[b, PdVars[d, etc]], c] - PdHold[PdT[b, PdVars[etc]] Pd[a, c], d] + PdT[b, PdVars[etc]] PdT[a, PdVars[c,d]]]+ e,
	a_. b_^n_. PdT[b_, PdVars[c_]] + e_. :> e + Simp[ PdHold[a b^(n+1)/(n+1), c]  - b^(n+1) Pd[a, c] / (n+1) ] /;n=!=-1,
	a_. PdT[b_, PdVars[etc___]]^n_. PdT[b_, PdVars[c_, etc___]] + e_. :> e + Simp[ PdHold[a PdT[b, PdVars[etc]]^(n+1) / (n+1), c] - PdT[b, PdVars[etc]]^(n+1) Pd[a, c] / (n+1) ] /;n=!=-1,
	
	h_. + g_. PdT[t_, PdVars[a_, b_, e___]]^2 :> With[{f=PdT[t, PdVars[e]]}, h + Simp[
		PdHold[g Pd[Pd[f,a],b]Pd[f,b], a] - PdHold[g Pd[Pd[f,a],a]Pd[f,b], b] - Pd[g,a]Pd[Pd[f,a],b]Pd[f,b] + Pd[g,b]Pd[Pd[f,a],a]Pd[f,b] + g Pd[Pd[f,a],a]Pd[Pd[f,b],b] ]],
	
  PdT[f_,PdVars[a_,e1___]]PdT[g_,PdVars[b_,e2___]]h_. + n_. /; Order[a,b]>=0 :> Simp[PdHold[PdT[f,PdVars[e1]] Pd[PdT[g,PdVars[e2]],b]h, a] - PdHold[PdT[f,PdVars[e1]] Pd[PdT[g,PdVars[e2]],a]h, b]
		+ Pd[PdT[f,PdVars[e1]],b]Pd[PdT[g,PdVars[e2]],a]h + PdT[f,PdVars[e1]] Pd[PdT[g,PdVars[e2]],a]Pd[h,b] - PdT[f,PdVars[e1]] Pd[PdT[g,PdVars[e2]],b] Pd[h,a]] + n,
	(* some special higher order rules *)
	x_. + f_. PdT[z_, PdVars[a_, e___]]PdT[z_, PdVars[b_, c_, e___]] /; Order[a,b]>=0 && Expand[f-(f/.{a->b,b->a})]===0 :>
		x + Simp[PdHold[f PdT[z, PdVars[a, e]]PdT[z, PdVars[b, e]]/2, c] - Pd[f,c]PdT[z, PdVars[a, e]]PdT[z, PdVars[b, e]]/2],
	x_. + f_. PdT[h_, PdVars[c_, e___]]PdT[h_, PdVars[a_, b_, e___]]PdT[h_, PdVars[a_, b_, e___]] /; Order[a,b]>=0 :> With[{g=PdT[h,PdVars[e]]},
		x + Simp[PdHold[f Pd[g,c]Pd[g,b]Pd[Pd[g,a],b] - f Pd[g,b]^2 Pd[Pd[g,a],c]/2 - Pd[f,a] Pd[g,b]^2 Pd[g,c]/2, a] 
		- PdHold[f Pd[g,c]Pd[g,b]Pd[Pd[g,a],a], b] + PdHold[f Pd[g,b]^2 Pd[Pd[g,a],a]/2, c]
		+ f Pd[g,c]Pd[Pd[g,a],a]Pd[Pd[g,b],b] - Pd[f,c]Pd[g,b]^2 Pd[Pd[g,a],a]/2 
		+ Pd[f,b]Pd[g,c]Pd[g,b]Pd[Pd[g,a],a] + Pd[Pd[f,a],a]Pd[g,c]Pd[g,b]^2/2 + Pd[f,a]Pd[Pd[g,a],c]Pd[g,b]^2]	],
	(*x_. + f_. g_ PdT[g_, PdVars[a_,b_,b_]] :> x + Simp[PdHold[f g Pd[Pd[g,a],b], b] - PdHold[f Pd[g,b]^2/2, a] - Pd[f,b] g Pd[Pd[g,a],b] + Pd[f,a]Pd[g,b]^2/2],*)
	x_. + f_. PdT[h_, PdVars[c_, e___]]PdT[h_, PdVars[a_, b_, e___]] /; Order[a,b]>=0 && Expand[f-(f/.{a->b,b->a})]===0 :> With[{g=PdT[h,PdVars[e]]},
		x + Simp[PdHold[f Pd[g,c]Pd[g,b], a] - PdHold[f Pd[g,a]Pd[g,b]/2, c] -Pd[f,a]Pd[g,c]Pd[g,b] + Pd[f,c]Pd[g,a]Pd[g,b]/2] ]} ~Join~ Normal[Pm2Rules])

Options[Ibp] = {"Rule":>IbpRules, "Rank"->IbpCountLeaf, "Level"->1}
Ibp[e_, OptionsPattern[]]:= try[OptionValue@"Rule", OptionValue@"Rank", OptionValue["Level"]][Simp@e]
IbpNB[e__]:= Block[{PdHold=0&}, Ibp[e]]

holdPtn=_PdHold|_IdHold
IbpCountLeaf[e_]:= Count[{e/.holdPtn->0}, PdT[v_[DE@0,___],PdVars[__]], Infinity] * 10^-7 + LeafCount[e/.holdPtn->0] * 10^-5 + Count[{e/.holdPtn->0}, Pm2[__]] * 10^-3 + Count[{e/.holdPtn->0}, Pm2[Times[f__], _] * 10^-1 ]
IbpCountTerm[e_]:=Length[expand2list[e/.holdPtn->0]] * 10^-5  + Count[{e/.holdPtn->0}, Pm2[__]] * 10^-3 + Count[{e/.holdPtn->0}, Pm2[Times[f__], _] * 10^-1 ]
IbpCountPt2[e_]:= Count[{e/.holdPtn->0}, PdT[_, PdVars[_DE, _DE, ___]], Infinity] + IbpCountLeaf[e] 
IbpCountPd2[e_]:= Count[{e/.holdPtn->0}, PdT[_, PdVars[IdxPtn, IdxPtn, ___]], Infinity] + IbpCountLeaf[e]
IbpVar[var_][e_]:= 10000*Count[{e/.holdPtn->0}, Pd[Pd[Pd[a_/;!FreeQ[a, var], _],_],_], Infinity] + 100*Count[{e/.holdPtn->0}, Pd[Pd[a_/;!FreeQ[a, var], _],_], Infinity] + Count[{e/.holdPtn->0}, Pd[a_/;!FreeQ[a, var], _], Infinity] + IbpCountLeaf[e]
IbpStd2[e_]:= IbpCountPt2[e]*1000 + IbpCountPd2[e]*100 + Count[{e/.holdPtn->0}, v_*Pd[v_,_]*_ | PdT[v_, PdVars[a__]]*PdT[v_, PdVars[b_,a__]]*_, Infinity]*10 + Count[{e/.holdPtn->0}, PdT[v_[DE@0,___],PdVars[DE@0,___]], Infinity] + IbpCountLeaf[e]

IbpReduceOrder[vars_List][e_]:=Module[{eOrderList, tmp},
	eOrderList = Count[{#}, Alternatives@@vars, Infinity] & /@ times2prod@expand2list[e+tmp /.holdPtn->0];
	Total[100^(5-#)&/@eOrderList]-100^5 + IbpCountLeaf[e] + IbpCountTerm[e]]

IbpVariation[e_, v_]:= FixedPoint[Replace[#, a_. + b_.*PdT[f_, PdVars[i_, j___]] /; FreeQ[b, v] && ! FreeQ[f, v] :> a - Simp[PdT[f, PdVars[j]]*Pd[b, i]]] &, Simp[e]]

End[]
EndPackage[]
