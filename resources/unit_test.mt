(* Mathematica Test File *)


(* ::Section:: *)
(* Tests for tensor.m *)

ClearAll[u, d, dimTest, f, f1, f2, f3, g, undefined]

(* ::Subsection:: *)
(* DeclareIdx *)

DeclareIdx[{u,d}, dimTest, LatinIdx, Blue]
Test[
	MemberQ[IdxList, u] && MemberQ[IdxList, d] && MemberQ[IdxUpList, u] && MemberQ[IdxDnList, d], 
	True, TestID->"DeclareIdx idx lists"]
Test[
	MatchQ[u["a"], IdxPtn] && MatchQ[d["a"], IdxPtn] && MatchQ[u["a"], IdxUpPtn] && MatchQ[d["a"], IdxDnPtn], 
	True, TestID->"DeclareIdx idx patterns"]
Test[
	IdxDual[u]==d && IdxDual[d]==u && IdxSet[u]==LatinIdx && IdxSet[d]==LatinIdx
		&& IdxColor[u]==Blue && IdxColor[d]==Blue && Dim[u]==dimTest && Dim[d]==dimTest, 
	True, TestID->"DeclareIdx properties"]

(* ::Subsection:: *)
(* DeclareExplicitIdx *)

DeclareExplicitIdx[{ue, de}, Brown]
Test[MemberQ[IdxNonSumList, ue] && MemberQ[IdxNonSumList, de] && MatchQ[ue[0], IdxNonSumPtn] && MatchQ[de[0], IdxNonSumPtn], 
	True, TestID->"DeclareExplicitIdx"]

(* ::Subsection:: *)
(* Dta *)

Test[f[u@"a", f1[u@"b"]]Dta[u@"b", u@"c"], f[u@"a", f1[u@"c"]], TestID->"Dta up-up, with nest func"]
Test[f[u@"a", d@"b"]Dta[u@"b", d@"c"], f[u@"a", d@"c"], TestID->"Dta up-dn"]
Test[f[d@"a", d@"b"]Dta[d@"b", d@"c"], f[d@"a", d@"c"], TestID->"Dta dn-dn"]
Test[Dta[u@"a", u@"c"]Dta[u@"b", u@"c"], Dta[u@"a", u@"b"], TestID->"Dta-Dta contraction up-up"]
Test[Dta[u@"a", d@"c"]Dta[d@"b", u@"c"], Dta[u@"a", d@"b"], TestID->"Dta-Dta contraction up-dn"]
Test[Dta[d@"a", d@"c"]Dta[d@"b", d@"c"], Dta[d@"a", d@"b"], TestID->"Dta-Dta contraction dn-dn"]
Test[Dta[u@"a", u@"a"]==dimTest && Dta[u@"a", d@"a"]==dimTest && Dta[d@"a", d@"a"]==dimTest 
	&& Dta[u@"a", u@"b"]Dta[u@"a", u@"b"]==dimTest && Dta[u@"a", u@"b"]Dta[d@"a", d@"b"]==dimTest
	&& Dta[u@"a", d@"b"]Dta[u@"a", d@"b"]==dimTest
	&& Dta[u@"a", u@"b"]Dta[u@"b", u@"c"]Dta[u@"c", u@"d"]Dta[u@"d", u@"a"]==dimTest,
	True, TestID->"Dta sum"]
Test[Dta[ue@1, de@0]==0 && Dta[ue@1, de@1]==1, True, TestID->"Dta explicit idx"]

(* ::Subsection:: *)
(* LeviCivita *)

DeclareIdx[{u3,d3}, 3, LatinIdx, Brown]
Test[LeviCivita[u3@"a", u3@"b", u3@"c"] LeviCivita[d3@"d", d3@"e", d3@"f"], -Hold[Dta][d3["d"], u3["c"]] Hold[Dta][d3["e"], u3["b"]] Hold[Dta][
   d3["f"], u3["a"]] + 
 Hold[Dta][d3["d"], u3["b"]] Hold[Dta][d3["e"], u3["c"]] Hold[Dta][
   d3["f"], u3["a"]] + 
 Hold[Dta][d3["d"], u3["c"]] Hold[Dta][d3["e"], u3["a"]] Hold[Dta][
   d3["f"], u3["b"]] - 
 Hold[Dta][d3["d"], u3["a"]] Hold[Dta][d3["e"], u3["c"]] Hold[Dta][
   d3["f"], u3["b"]] - 
 Hold[Dta][d3["d"], u3["b"]] Hold[Dta][d3["e"], u3["a"]] Hold[Dta][
   d3["f"], u3["c"]] + 
 Hold[Dta][d3["d"], u3["a"]] Hold[Dta][d3["e"], u3["b"]] Hold[Dta][
   d3["f"], u3["c"]], TestID->"2 LeviCivita's"]
Test[LeviCivita[u3@"a", u3@"b", u3@"c"] LeviCivita[d3@"a", d3@"d", d3@"e"], -Hold[Dta][d3["d"], u3["c"]] Hold[Dta][d3["e"], u3["b"]] + 
 Hold[Dta][d3["d"], u3["b"]] Hold[Dta][d3["e"], u3["c"]], TestID->"LeviCivita contract 1"]
Test[LeviCivita[u3@"a", u3@"b", u3@"c"] LeviCivita[d3@"a", d3@"b", d3@"d"], 2 Hold[Dta][d3["d"], u3["c"]], TestID->"LeviCivita contract 2"]
Test[LeviCivita[u3@"a", u3@"b", u3@"c"] LeviCivita[d3@"a", d3@"b", d3@"c"], 6, TestID->"LeviCivita contract 3"]

UseMetric[g3, {u3,d3}]
Test[LeviCivita[u3@"a", u3@"b", u3@"c"] LeviCivita[u3@"d", u3@"e", u3@"f"], -(g3[u3["a"], u3["f"]]*g3[u3["b"], u3["e"]]*g3[u3["c"], u3["d"]]) + g3[u3["a"], u3["e"]]*g3[u3["b"], u3["f"]]*g3[u3["c"], u3["d"]] + g3[u3["a"], u3["f"]]*g3[u3["b"], u3["d"]]*g3[u3["c"], u3["e"]] - g3[u3["a"], u3["d"]]*g3[u3["b"], u3["f"]]*g3[u3["c"], u3["e"]] - g3[u3["a"], u3["e"]]*g3[u3["b"], u3["d"]]*g3[u3["c"], u3["f"]] + g3[u3["a"], u3["d"]]*g3[u3["b"], u3["e"]]*g3[u3["c"], u3["f"]], TestID->"LeviCivita up up"]

(* ::Subsection:: *)
(* Sym, Asym *)

Test[Sym[f[d@"a",d@"b"]],f[d@"a",d@"b"]+f[d@"b",d@"a"], TestID->"Sym"]
Test[AntiSym[f[d@"a",d@"b"]],f[d@"a",d@"b"]-f[d@"b",d@"a"], TestID->"AntiSym"]

(* ::Subsection:: *)
(* Pd *)

Test[Pd[Dta[u@"a", d@"b"], d@"c"]==0 && Pd[Sin[1], d@"c"]==0&& Pd[dimTest, d@"c"]==0, 
	True, TestID->"Pd on constants"]
Test[Pd[f[u@"a"]g+h[u@"a"], d@"b"], 
	Pd[f[u@"a"], d@"b"]g+f[u@"a"]Pd[g, d@"b"]+Pd[h[u@"a"], d@"b"], TestID->"Pd add and times"]
Test[Pd[undefined, d@"x"], Pd[undefined, d@"x"], TestID->"PD on unknown var"]
Test[Pd[a_,d@b_]:>f[a,b],Pd[a_,d@b_]:>f[a,b], TestID->"Pattern is not considered as background or constant"]

(* ::Subsection:: *)
(* SimpF *)

Test[Simp[f[u@"x", d@"b"] f1[d@"b"], "Method"->"Fast"], f[u["x"], d["a"]] f1[d["a"]], TestID->"SimpF re-arrange idx"]

(* ::Subsection:: *)
(* SimpM *)
DeclareSym[f3, {d, d, d, d}, Symmetric[{1, 2}]];
DeclareSym[f3, {d, d, d, d}, Antisymmetric[{3, 4}]];
Test[f3[d@"i", d@"j", d@"i", d@"j"] // Simp[#, "Method"->"MOnly"]&, 0, TestID->"SimpM symmetric"]
Test[Pd[f3[d@"i", d@"j", d@"i", d@"j"],d@"k"] // Simp[#, "Method"->"MOnly"]&, 0, TestID->"SimpM antisymmetric"]
Test[Pd[f3[d@"i", de@0, d@"i", de@0],d@"k"] // Simp[#, "Method"->"MOnly"]&, Pd[f3[d["a"], de[0], d["a"], de[0]], d["k"]], TestID->"SimpM with explicit idx"]
Test[c[D2@"b", D2@"c", U2@"a"] A[U2@"b", DN@"\[Mu]"] A[U2@"c",DN@"\[Nu]"] // Simp, 
	A[U2["b"], DN["\[Mu]"]] A[U2["c"], DN["\[Nu]"]] c[D2["b"], D2["c"], U2["a"]], TestID->"Simp with free idx sorted"]
(* ::Subsection:: *)
(* private functions in tensor.m and util.m *)

Begin["MathGR`tensor`Private`"]
Test[plus2listRaw[1+a+c], {1, a, c}, TestID->"plus2listRaw"]
Test[plus2list[1+2(a+c)], {1, 2a, 2c}, TestID->"plus2list"]
Test[apply2term[testf, 1+2(a+c)], testf[1]+testf[2a]+testf[2c], TestID->"apply2term"]
Test[getSampleTerm[2(a+c)], 2a, TestID->"getSampleTerm"]
Test[times2prod[a+b^3 c+d^n], a+prod[b,b,b,c]+d^n, TestID->"times2prod"]
Test[prod2times[a+prod[b,b,b,c]+d^n], a+b^3 c+d^n, TestID->"prod2times"]
Test[f[a,b,c]/.{a,b,c}~replaceTo~{x,y,z}, f[x,y,z], TestID->"replaceTo"]

Test[idx[a[u@"a", d@"b"]Pd[f[u@"c",u@"b"],d@"a"]], {"a","b","c","b","a"}, TestID->"idx"]
Test[idx[a[u@"a", d@"b"]Pd[f[u@"c",u@"b"],d@"a"]f[d@"x"]^2], {"a","b","x","x","c","b","a"}, TestID->"idx2"]
Test[free[a[u@"a", d@"b"]Pd[f[u@"c",u@"b"],d@"a"]f[d@"x"]^2], {"c"}, TestID->"free"]
Test[dummy[a[u@"a", d@"b"]Pd[f[u@"c",u@"b"],d@"a"]f[d@"x"]^2], {"a","b","x"}, TestID->"dummy"]
Test[pd2pdts[Pd[f[u@"a"],d@"a"]], pdts[1][f][u@"a", d@"a"], TestID->"Pd to pdts"]
Test[pdts2pd[pdts[1][f][u@"a", d@"a"]], Pd[f[u@"a"],d@"a"], TestID->"pdts to Pd"]

Test[rmNE[{ue@0,u@"a",d@"b",de@1,d@"c"}], {u@"a",d@"b",d@"c"}, TestID->"rmNE"]
End[]

(* ::Section:: *)
(* Tests for gr.m *)

UseMetric[g, {u,d}]

(* ::Subsection:: *)
(* MetricContract *)

Test[MetricContract[f[UG@1, DG@2]f1[UG@1, DG@2]] // Simp, 
	f[u["a"], d["b"]]*f1[u["c"], d["d"]]*g[d["a"], d["c"]]*g[u["b"], u["d"]], TestID->"MetricContract"]

(* ::Subsection:: *)
(* Affine and curvature *)

Test[Affine[u@"a",d@"b",d@"c"]//Simp,
	-(g[u["a"], u["d"]]*Pd[g[d["b"], d["c"]], d["d"]])/2 + (g[u["a"], u["d"]]*Pd[g[d["b"], d["d"]], d["c"]])/2 + (g[u["a"], u["d"]]*Pd[g[d["c"], d["d"]], d["b"]])/2,
	TestID->"Affine"]
Test[R[]//Simp,
	(3*g[u["a"], u["b"]]*g[u["c"], u["d"]]*g[u["e"], u["f"]]*Pd[g[d["a"], d["c"]], d["e"]]*Pd[g[d["b"], d["d"]], d["f"]])/4 - (g[u["a"], u["b"]]*g[u["c"], u["d"]]*g[u["e"], u["f"]]*Pd[g[d["a"], d["c"]], d["f"]]*Pd[g[d["b"], d["e"]], d["d"]])/2 - g[u["a"], u["b"]]*g[u["c"], u["d"]]*g[u["e"], u["f"]]*Pd[g[d["a"], d["c"]], d["d"]]*Pd[g[d["b"], d["e"]], d["f"]] - (g[u["a"], u["b"]]*g[u["c"], u["d"]]*g[u["e"], u["f"]]*Pd[g[d["a"], d["b"]], d["e"]]*Pd[g[d["c"], d["d"]], d["f"]])/4 + g[u["a"], u["b"]]*g[u["c"], u["d"]]*g[u["e"], u["f"]]*Pd[g[d["a"], d["b"]], d["d"]]*Pd[g[d["c"], d["e"]], d["f"]] - g[u["a"], u["b"]]*g[u["c"], u["d"]]*Pd[Pd[g[d["a"], d["b"]], d["c"]], d["d"]] + g[u["a"], u["b"]]*g[u["c"], u["d"]]*Pd[Pd[g[d["a"], d["c"]], d["b"]], d["d"]],
	TestID->"Ricci scalar"]

Test[CovD[R[d@"a", d@"b", d@"c", d@"d"], d@"e"] + CovD[R[d@"a", d@"b", d@"d", d@"e"], d@"c"] + CovD[R[d@"a", d@"b", d@"e", d@"c"], d@"d"] // Simp, 0, TestID->"Second Bianchi of Riemann"]
	
(* ::Subsection:: *)
(* CovD *)

Test[CovD[f2 f[u@"a",d@"b"]f1[d@"c"] ,d@"d"]//Simp,
	f[u["a"], d["b"]]*f1[d["c"]]*Pd[f2, d["d"]] + f2*f1[d["c"]]*Pd[f[u["a"], d["b"]], d["d"]] + f2*f[u["a"], d["b"]]*Pd[f1[d["c"]], d["d"]] + (f2*f[u["a"], d["e"]]*f1[d["c"]]*g[u["e"], u["f"]]*Pd[g[d["b"], d["d"]], d["f"]])/2 - (f2*f[u["a"], d["e"]]*f1[d["c"]]*g[u["e"], u["f"]]*Pd[g[d["b"], d["f"]], d["d"]])/2 + (f2*f[u["a"], d["b"]]*f1[d["e"]]*g[u["e"], u["f"]]*Pd[g[d["c"], d["d"]], d["f"]])/2 - (f2*f[u["a"], d["b"]]*f1[d["e"]]*g[u["e"], u["f"]]*Pd[g[d["c"], d["f"]], d["d"]])/2 - (f2*f[u["e"], d["b"]]*f1[d["c"]]*g[u["a"], u["f"]]*Pd[g[d["d"], d["e"]], d["f"]])/2 - (f2*f[u["a"], d["e"]]*f1[d["c"]]*g[u["e"], u["f"]]*Pd[g[d["d"], d["f"]], d["b"]])/2 - (f2*f[u["a"], d["b"]]*f1[d["e"]]*g[u["e"], u["f"]]*Pd[g[d["d"], d["f"]], d["c"]])/2 + (f2*f[u["e"], d["b"]]*f1[d["c"]]*g[u["a"], u["f"]]*Pd[g[d["d"], d["f"]], d["e"]])/2 + (f2*f[u["e"], d["b"]]*f1[d["c"]]*g[u["a"], u["f"]]*Pd[g[d["e"], d["f"]], d["d"]])/2,
	TestID->"CovD"]
	
(* ::Section:: *)
(* Tests for ibp.m *)

Test[Ibp[y Pd[x, d@"a"] + x Pd[y, d@"a"] + f[d@"a"] + xx yy Pd[zz, d@"a"] +   xx zz Pd[yy, d@"a"] + xxx Pd[yyy, d@"a"]],
	f[d@"a"] - yy zz Pd[xx, d["a"]] + xxx Pd[yyy, d["a"]] +  PdHold[x y, d["a"]] + PdHold[xx yy zz, d["a"]], TestID->"Ibp CountLeaf"]
	
Test[Ibp[y Pd[Pd[x, de@0], de@0], IbpCountPt2], -Pd[x, de[0]] Pd[y, de[0]] + PdHold[y Pd[x, de[0]], de[0]], TestID->"Ibp CountPt2"]

Test[Ibp[y Pd[x, d@"i"], IbpVar[x]], -x Pd[y, d["i"]] + PdHold[x y, d["i"]], TestID->"IbpVar"]

(* ::Section:: *)
(* Cosmic perturbations *)

Get["MathGR/util.m"]
Get["MathGR/ibp.m"]
Get["MathGR/frwadm.m"]
DeclareIdx[{UP, DN}, DefaultDim, LatinIdx, Black]
PdHold[__] := 0
phi = phi0
(*Pd[phi0|Pd[phi0,DE@0]|Pd[Pd[phi0,DE@0],DE@0],DN@_]:=0*)
Pd[phi0|Pd[phi0,DE@0],DN@_]:=0
s012 = Sqrtg (RADM[]/2 + DecompG2H[X[phi]] - V[phi] ) // SS[2]
Print["Result of s012 =========="];Print[s012]
s1 = s012 // OO[1]
Print["Result of s1 =========="];Print[s1]
SimpHook =  SimpHook~Union~(SolveExpr[{D[s1, \[Alpha]] == 0, D[Ibp[s1, IbpVar[\[Zeta]]], \[Zeta]] == 0}, {V[phi0], Pd[phi0, DE@0]^2}][[1]])
s2 = s012 // OO[2] // Fourier2
Print["Result of s2 =========="];Print[s2]
solCons =  Solve[{D[s2, \[Alpha]] == 0, D[s2, \[Beta]] == 0, D[s2, b[DN@"a"]] == 0}, {\[Alpha], \[Beta], b[DN@"a"]}][[1]]
s2Solved = s2 /. solCons // Ibp[#, IbpStd2] &
Print["Result of s2Solved =========="];Print[s2Solved]
Test[s2Solved, -(a*k^2*\[Epsilon]*\[Zeta]^2) + a^3*\[Epsilon]*Pd[\[Zeta], DE[0]]^2, TestID->"zeta gauge 2nd order action"]
