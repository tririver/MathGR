(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`util`", {"MathGR`tensor`"}]

SolveExpr::usage = "SolveExpr[eqs, exprs] is a wraper of Solve[eqs, exprs], but now exprs can now be composed expression instead of atom"
TReplace::usage = "TensorReplace[expr, rule] replaces expr using rule. times2prod is used to avoid power of dummy indices"
TPower::usage = "TPower[expr, n] (where n is an integer) gives nth power of a tensor, taking care of the dummy indices"
TSeries::usage = "TSeries[expr, {Eps, 0, n}] expands tensor expr wrt Eps"
Eps::usage = "The perturbative expansion varible"
CollectEps::usage = "CollectEps[vars, operation] First (outer) collects Eps, then (inner) collects vars, then apply operation"
SS::usage = "SS[n] gives up to order n series in Eps"
OO::usage = "OO[n] gives order n result in Eps"
k::usage = "Default variable for Fourier transformation."
LocalToK::usage = "LocalToK[term, optional:id] transforms a local term into Fourier space."

Begin["`Private`"]
Needs["MathGR`utilPrivate`"]

PdT[Eps, _]:=0

SolveExpr[eqs_, exprsRaw_] := Module[{exprs = Flatten@{exprsRaw}, repList},
  repList = Unique[] /@ exprs;
  Solve[eqs /. (exprs~replaceTo~repList), repList] /. (repList~replaceTo~exprs)]

TReplace[expr_, rule_]:= prod2times[times2prod[expr] /. f_prod:>Map[#/.rule&, f] //. rule]
TReplace[rule_][expr_]:= TReplace[expr, rule]
TPower[expr_, n_Integer]:= Power[Product[expr, {i,Abs@n}],Sign@n]

applyProtect[f_, e_]:=Module[{eLocal}, f //. g_ e^m_. /; FreeQ[g,protected] :> protectProd[g] eLocal^m /. eLocal -> e ];
protectProd[f_]:=protected[Times@@#[[1]]]Times@@#[[2]]&@ {Select[#,FreeQ[#,Eps]&],Select[#,!FreeQ[#,Eps]&]} &@ times2list @ f;
TSeries[f_,{e_,e0_,n_}]:=Series[applyProtect[f,e],{e,e0,n}]/.{protected[g_]^m_:>Product[SimpUq[g],{i,m}], protected->SimpUq};

CollectEps[vars_:{tmp}, op_:Simp][f_]:= Collect[f, Eps, Collect[#, vars, op]&]
SS[n_, vars_:{tmp}, op_:Simp][f_]:= CollectEps[vars, op]@Normal@TSeries[f,{Eps,0,n}]
OO[n_, vars_:{tmp}, op_:Simp][f_]:= CollectEps[vars, op]@Coefficient[SS[n, vars, op][f], Eps, n]

Options[LocalToK]={"Momentum"->k};
LocalToK[expr_, id_:DN, OptionsPattern[]]:= apply2term[LocalToKTerm[#, id, OptionValue@"Momentum"]&, expr];

LocalToKTerm[term_, id_: DN, kk_: k]:= Module[{cnt = 0, vars, pvars, testId, ruleK, ruleP, ruleR},
  vars = DeleteDuplicates[Variables[term] /. PdT[f_, __] :> f];
  pvars = Alternatives @@ Select[vars, Pd[#, id@testId] =!= 0 &];
  ruleK := (v : pvars) :> (cnt++; v[kk[cnt]]);
  ruleP := PdT[f_[kf_kk], PdVars[i : (_id ..), etc___]] :> Apply[Times, kf /@ {i}] PdT[f[kf], PdVars[etc]];
  ruleR := f_[i:(IdxPtn|_UE|_DE) ..][k0_kk] :> f[k0][i];
  term /. ruleK /. ruleP /. ruleR];

End[]
EndPackage[]