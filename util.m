(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`util`", {"MathGR`tensor`"}]

SolveExpr::usage = "SolveExpr[eqs, exprs] is a wraper of Solve[eqs, exprs], but now exprs can now be composed expression instead of atom"
TReplace::usage = "TensorReplace[expr, rule] replaces expr using rule. times2prod is used to avoid power of dummy indices"
Eps::usage = "The perturbative expansion varible"
CollectEps::usage = "CollectEps[vars, operation] First (outer) collects Eps, then (inner) collects vars, then apply operation"
SS::usage = "SS[n] gives up to order n series in Eps"
OO::usage = "OO[n] gives order n result in Eps"
Fourier2::usage = "Fourier2[expr] is Fourier transformation (for 2nd order perturbation only)"
k::usage = "Momentum used in Fourier transformation"

Begin["`Private`"]
Needs["MathGR`utilPrivate`"]

PdT[k|Eps, PdVars[__]]:=0

SolveExpr[eqs_, exprsRaw_] := Module[{exprs = Flatten@{exprsRaw}, repList},
  repList = Unique[] /@ exprs;
  Solve[eqs /. (exprs~replaceTo~repList), repList] /. (repList~replaceTo~exprs)]

TReplace[expr_, rule_]:= prod2times[times2prod[expr]/.rule]

CollectEps[vars_:{tmp}, op_:Simp][f_]:= Collect[f, Eps, Collect[#, vars, op]&]
SS[n_, vars_:{tmp}, op_:Simp][f_]:= CollectEps[vars, op]@Normal@Series[f,{Eps,0,n}]
OO[n_, vars_:{tmp}, op_:Simp][f_]:= CollectEps[vars, op]@Coefficient[SS[n, vars, op][f], Eps, n]
	
fourier2RuleList = Dispatch@{PdT[f_, PdVars[DN@i_, DN@i_, j___]] :> -k^2 PdT[f, PdVars[j]],
 PdT[f_, PdVars[DN@i_, a___]] PdT[g_, PdVars[DN@i_, b___]] :>  k^2 PdT[f, PdVars[a]] PdT[g, PdVars[b]],
 PdT[f_, PdVars[DN@i_, j___]]^2 :> k^2 PdT[f, PdVars[j]]^2,
 PdT[f_, PdVars[DN@i_, j___]] b_[DN@i_] :> -I k[DN@i] PdT[f, PdVars[j]] b[DN@i]}

Fourier2[e_]:= (e//.fourier2RuleList//Expand)//.fourier2RuleList

End[]
EndPackage[]