(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`util`", {"MathGR`tensor`"}]

SolveExpr::usage = "SolveExpr[eqs, exprs] is a wraper of Solve[eqs, exprs], but now exprs can now be composed expression instead of atom"

Eps::usage = "The perturbative expansion varible"
CollectEps::usage = "CollectEps[vars, operation] First (outer) collects Eps, then (inner) collects vars, then apply operation"
SS::usage = "SS[n] gives up to order n series in Eps"
OO::usage = "OO[n] gives order n result in Eps"
Fourier2::usage = "Fourier2[expr] is Fourier transformation (for 2nd order perturbation only)"
k::usage = "Momentum used in Fourier transformation"

Begin["`Private`"]
Needs["MathGR`utilPrivate`"]

(Pd[#,_]:=0) &/@ {k, Eps}

SolveExpr[eqs_, exprsRaw_] := Module[{exprs = Flatten@{exprsRaw}, repList},
  repList = Unique[] /@ exprs;
  Solve[eqs /. (exprs~replaceTo~repList), repList] /. (repList~replaceTo~exprs)]

CollectEps[vars_:{}, op_:Simp][f_]:= Collect[f, Eps, Collect[#, vars, op]&]
SS[n_, vars_:{}, op_:Simp][f_]:= CollectEps[vars, op]@Normal@Series[op@f,{Eps,0,n}]
OO[n_, vars_:{}, op_:Simp][f_]:= CollectEps[vars, op]@Coefficient[SS[n, vars, op][f], Eps, n]

fourier2RuleList = Dispatch@{Pd[Pd[f_, DN@i_], DN@i_]:> -k^2 f, Pd[a_, DN@i_]Pd[b_, DN@i_]:> k^2 a b, Pd[a_, DN@i_]b_[DN@i_]:> -I k[DN@i] a b[DN@i],
	Pd[Pd[a_, DN@i_], DN@j_]Pd[Pd[b_, DN@i_], DN@j_]:> k^4 a b, Pd[Pd[a_, DN@i_], DN@j_]^2:> k^4 a^2, Pd[a_, DN@i_]^2:> k^2 a^2,
	Pd[f_[DN@i_],DN@j_]Pd[g_[DN@j_],DN@i_]:> k[DN@i]k[DN@j]f[DN@i]g[DN@j], Pd[Pd[f_[DN@i_],DN@a_],DN@j_]Pd[Pd[g_[DN@j_], DN@b_],DN@i_]:> k[DN@i]k[DN@j]Pd[f[DN@i],DN@a]Pd[g[DN@j],DN@b]}
Fourier2[e_]:= (e//.fourier2RuleList//Expand)//.fourier2RuleList

End[]
EndPackage[]