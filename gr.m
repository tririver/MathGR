(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`gr`", {"MathGR`tensor`"}]

WithMetric::usage = "WithMetric[g, expr] calculates expr with metric g. It does not change the default metric"
UseMetric::usage = "UseMetric[g] chooses g for contraction and calculation of affine ane curvatures. UseMetric[g, False] set attributes for g, but don't set g as default metric."
Metric::usage = "The current metric for contraction, affine and curvatures"
g::usage = "The default metric for contraction, affine and curvatures"
IdxOfMetric::usage = "The indices used with the metric"
DG::usage = "MetricContract pairs with lower idx"
UG::usage = "MetricContract pairs with upper idx"
MetricContract::usage = "MetricContract[expr] contracts expr with metric. The contraction variables are marked as UG pairs or DG pairs"

CovD::usage = "CovD[t, DN@idx] is covariant derivative"
Dsquare::usage = "Dsquate[f] is the covariant derivative squared"
Affine::usage = "Affine[UP@a, DN@b, DN@c] is the affine connection calculated from Metric"
R::usage = "Riemann, Ricci tensors and Ricci scalar"
Rsimp::usage = "Ricci tensor and Ricci scalar, pre-simplified into metric"
G::usage = "The Einstein tensor"
K::usage = "Extrinic curvature"
KK::usage = "[KK]"
RADM::usage = "The ADM curvature, equal to R up to a total derivative"
LapseN::usage = "The lapse function"
ShiftN::usage = "The shift vector"
X::usage = "X[field] gives -g[UP@a, UP@b]Pd[field,DN@a]PD[field,DN@b]/2"

Begin["`Private`"]
Needs["MathGR`utilPrivate`"]

iu:=IdxOfMetric[[1]]
id:=IdxOfMetric[[2]]
isu[a_]:=Head@a===iu
isd[a_]:=Head@a===id

SetAttributes[{WithMetric, UseMetric}, HoldAll]

WithMetric[g_, idx_:{UP, DN}, e_]:= (UseMetric[g, idx, "SetAsDefault"->False]; 
	Block[{Metric=g, IdxOfMetric=idx}, e])
Options[UseMetric]={"SetAsDefault"->True}
UseMetric[g_, idx_:{UP, DN}, OptionsPattern[]]:= Module[{u=idx[[1]], d=idx[[2]], ids},
	If[OptionValue["SetAsDefault"], Metric = g; IdxOfMetric = idx]; (* When default=False, only set attributes, but don't set Metric *)
	DeclareSym[g, {u,u}, Symmetric[{1,2}]];
	DeclareSym[g, {d,d}, Symmetric[{1,2}]];
	(*g /: g[u@a_, d@b_]:= Dta[u@a, d@b];*) (* this is replaced by below because say, g[_UTot, _DTot] should also have g[_U1, _D1]=Dta*)
	If[Head@g[u@"a", d@"b"]===g (* g has not transformed to other things *), g /: g[i_@a_, j_@b_]/;i===IdxDual@j := Dta[i@a,j@b]];
	If[Head@g[u@"a", u@"b"]===g && Head@g[d@"a", d@"b"]===g, g /: g[u@a_, u@c_]g[d@c_, d@b_]:= Dta[u@a, d@b]];
	If[Head@Pd[g[u@"a", u@"b"], d@"c"]===PdT, g /: Pd[g[u@m_, u@a_], d@l_]:= -g[u@#1, u@a]g[u@#2, u@m]Pd[g[d@#1, d@#2], d@l] &@Uq[2];];
	If[IntegerQ[Dim@u],
		DeclareSym[LeviCivita, ConstantArray[#, d], Antisymmetric[All]]& /@ ids;
		LeviCivita /: LeviCivita[a:((u|d)[_]..)]*LeviCivita[b:((u|d)[_]..)]:= DtaGen[a, b, "DtaGenDta"->g]; ]]

UseMetric[g]

MetricContract[e_]:= mcTerm~apply2term~e
mcTerm[tRaw_]:=Module[{t, cnt=1, idTab, metrics, tmp=Unique[]},
	t = times2prod[tRaw] /. {(f:UG|DG)[n_]:>f[n, cnt++]}; (* make contraction labels unique *)
	idTab = Cases[t, _UG|_DG, Infinity] // Gather[#,(#1/.f_[a_,b_]:>a)===(#2/.f_[a_,b_]:>a)&]&; (* construct idx list of the metric *)
	metrics = Times@@ReplaceAll[(Metric@@@idTab),{DG->UG,UG->DG}]; (* construct metric *)
	metrics*t /.{(f:UG|DG)[n_,m_]:>f[tmp[n,m]]}/.{UG->iu,DG->id} // prod2times]

freeUD:= Function[x,Intersection[x,MathGR`tensor`Private`free@#]] /@ {Cases[times2prod@#, iu[a_]:>a, Infinity], Cases[times2prod@#, id[a_]:>a, Infinity] }&
freeUDSample:= freeUD[getSampleTerm@#]&
CovD[t_, m_?isd]:=Module[{uf, df, uniq=Unique[]},
	{uf, df} = freeUDSample[Expand@t];
	Pd[t,m] + Sum[Affine[i,m,id@uniq](t/.i->iu@uniq),{i,iu/@uf}] - Sum[Affine[iu@uniq,m,i](t/.i->id@uniq),{i,id/@df}]]

With[{g:=Metric, r:=Affine},
	r[i_?isu, m_?isd, n_?isd]:= 1/2 g[i, iu@#](Pd[g[id@#, m], n] + Pd[g[id@#, n], m] - Pd[g[m, n], id@#]) &@Uq[1];
	R[l_?isu, m_?isd, n_?isd, s_?isd]:= Pd[r[l,m,s],n]-Pd[r[l,m,n],s]+r[iu@#,m,s]r[l,id@#,n]-r[iu@#,m,n]r[l,id@#,s] &@Uq[1];
	R[a_?isd, m_?isd, n_?isd, s_?isd]:= g[a, id@#]R[iu@#, m, n, s] &@Uq[1];
	R[m_?isd, n_?isd]:= R[iu@#, m, id@#, n] &@Uq[1];
	R[]:= R[DG@1,DG@1]//MetricContract;
	G[m_?isd, n_?isd]:= R[m,n] - 1/2 g[m,n] R[];
	K[i_?isd, j_?isd]:= 1/(2 LapseN)(Pd[g[i,j],DE@0]-CovD[ShiftN[i],j]-CovD[ShiftN[j],i]);
	K[]:= K[DG@1,DG@1]//MetricContract;
	KK[]:= K[DG@1,DG@2]K[DG@1,DG@2]//MetricContract;
	RADM[]:= R[]-K[]K[]+KK[];
	X[f_]:= -Pd[f,DG@1]Pd[f,DG@1]/2//MetricContract;
	Dsquare[f_]:= CovD[CovD[f, DG@1], DG@1]//MetricContract;
	(* Some pre-simplified quantities *)
	Rsimp[]:= (3*g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*g[iu[#5], iu[#6]]*Pd[g[id[#1], id[#3]], id[#5]]*   Pd[g[id[#2], id[#4]], id[#6]])/4 - (g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*g[iu[#5], iu[#6]]*   Pd[g[id[#1], id[#3]], id[#6]]*Pd[g[id[#2], id[#5]], id[#4]])/2 - g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*g[iu[#5], iu[#6]]*Pd[g[id[#1], id[#3]], id[#4]]*  Pd[g[id[#2], id[#5]], id[#6]] - (g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*g[iu[#5], iu[#6]]*   Pd[g[id[#1], id[#2]], id[#5]]*Pd[g[id[#3], id[#4]], id[#6]])/4 + g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*g[iu[#5], iu[#6]]*Pd[g[id[#1], id[#2]], id[#4]]*  Pd[g[id[#3], id[#5]], id[#6]] - g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*  Pd[Pd[g[id[#1], id[#2]], id[#3]], id[#4]] + g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*  Pd[Pd[g[id[#1], id[#3]], id[#2]], id[#4]] &@Uq[6];
	Rsimp[m_?isd, n_?isd]:= -(g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*Pd[g[m, n], id[#4]]*Pd[g[id[#1], id[#2]], id[#3]])/4 + (g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*Pd[g[m, n], id[#4]]*Pd[g[id[#1], id[#3]], id[#2]])/2 - (g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*Pd[g[id[#1], id[#3]], id[#4]]*Pd[g[id[#2], m], n])/2 + (g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*Pd[g[id[#1], n], id[#3]]*Pd[g[id[#2], m], id[#4]])/2 - (g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*Pd[g[id[#1], id[#3]], id[#4]]*Pd[g[id[#2], n], m])/2 + (g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*Pd[g[id[#1], id[#3]], n]*Pd[g[id[#2], id[#4]], m])/4 + (g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*Pd[g[id[#1], id[#2]], id[#4]]*Pd[g[id[#3], m], n])/4 - (g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*Pd[g[id[#1], n], id[#4]]*Pd[g[id[#3], m], id[#2]])/2 + (g[iu[#1], iu[#2]]*g[iu[#3], iu[#4]]*Pd[g[id[#1], id[#2]], id[#4]]*Pd[g[id[#3], n], m])/4 - (g[iu[#1], iu[#2]]*Pd[Pd[g[m, n], id[#1]], id[#2]])/2 + (g[iu[#1], iu[#2]]*Pd[Pd[g[id[#1], m], n], id[#2]])/2 + (g[iu[#1], iu[#2]]*Pd[Pd[g[id[#1], n], m], id[#2]])/2 - (g[iu[#1], iu[#2]]*Pd[Pd[g[id[#1], id[#2]], m], n])/2 &@Uq[4];
]

End[]

EndPackage[]