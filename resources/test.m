(* Test setup *)
startTestTime=SessionTime[]
testPassed={};
testFailed={};

streamMsg = OpenWrite["test_message.txt"];
$Messages = {streamMsg};

SetAttributes[test,HoldAll]
testPrecision=10^-7;
test[in_,out_,tagRaw_:"Unspecified"]:=Module[{tag},
  tag=If[tagRaw==="Unspecified",HoldForm@in, tagRaw];
  If[in==out || Abs[in-out] <= testPrecision,
    testPassed~AppendTo~tag; Return[]];
  testFailed~AppendTo~{tag,
      "\n\tInput: " <> (ToString@HoldForm@InputForm@in) <>
      "\n\tCalculated: " <> (ToString@InputForm@in) <>
      "\n\tExpected: " <> (ToString@InputForm@out)}; Last@testFailed]

testReport[]:= Module[{str="", addLine},
  addLine:=(str=str<>Apply[StringJoin, ToString/@{##}]<>"\n")&;
  addLine["\nTest Report on ", DateString[]];
  addLine["Number of tests: ", Length@testPassed + Length@testFailed, "\n"];
  If[Length@testFailed===0,
    addLine["All tests passed."],
    addLine["Failed tests: ", Length@testFailed]; addLine[#1, "    ", #2]& @@@ testFailed];
  Print@OutputForm@str;
  Export["test_result.txt", str]];

<<"MathGR/MathGR.m"

(* ::Section:: *)
(* Tests for tensor.m *)

ClearAll[u, d, dimTest, f, f1, f2, f3, g, undefined]

(* ::Subsection:: *)
(* DeclareIdx *)

DeclareIdx[{u,d}, dimTest, LatinIdx, Blue]
test[
  MemberQ[IdxList, u] && MemberQ[IdxList, d] && MemberQ[IdxUpList, u] && MemberQ[IdxDnList, d],
  True, "DeclareIdx idx lists"]
test[
  MatchQ[u["a"], IdxPtn] && MatchQ[d["a"], IdxPtn] && MatchQ[u["a"], IdxUpPtn] && MatchQ[d["a"], IdxDnPtn],
  True, "DeclareIdx idx patterns"]
test[
  IdxDual[u]==d && IdxDual[d]==u && IdxSet[u]==LatinIdx && IdxSet[d]==LatinIdx
      && IdxColor[u]==Blue && IdxColor[d]==Blue && Dim[u]==dimTest && Dim[d]==dimTest,
  True, "DeclareIdx properties"]

(* ::Subsection:: *)
(* Dta *)

test[f[u@"a", f1[u@"b"]]Dta[u@"b", u@"c"], f[u@"a", f1[u@"c"]], "Dta up-up, with nest func"]
test[f[u@"a", d@"b"]Dta[u@"b", d@"c"], f[u@"a", d@"c"], "Dta up-dn"]
test[f[d@"a", d@"b"]Dta[d@"b", d@"c"], f[d@"a", d@"c"], "Dta dn-dn"]
test[f[u@"a", u@"b"]Dta[d@"b", d@"c"], f[u@"a", u@"c"], "Dta does not raise/lower idx"]
test[Dta[u@"a", u@"c"]Dta[u@"b", u@"c"], Dta[u@"a", u@"b"], "Dta-Dta contraction up-up"]
test[Dta[u@"a", d@"c"]Dta[d@"b", u@"c"], Dta[u@"a", d@"b"], "Dta-Dta contraction up-dn"]
test[Dta[d@"a", d@"c"]Dta[d@"b", d@"c"], Dta[d@"a", d@"b"], "Dta-Dta contraction dn-dn"]
test[Dta[u@"a", u@"a"]==dimTest && Dta[u@"a", d@"a"]==dimTest && Dta[d@"a", d@"a"]==dimTest
    && Dta[u@"a", u@"b"]Dta[u@"a", u@"b"]==dimTest && Dta[u@"a", u@"b"]Dta[d@"a", d@"b"]==dimTest
    && Dta[u@"a", d@"b"]Dta[u@"a", d@"b"]==dimTest
    && Dta[u@"a", u@"b"]Dta[u@"b", u@"c"]Dta[u@"c", u@"d"]Dta[u@"d", u@"a"]==dimTest,
  True, "Dta sum"]
test[Dta[UE@1, DE@0]==0 && Dta[UE@1, DE@1]==1, True, "Dta explicit idx"]

test[DtaGen[UP@"a", UP@"b", DN@"m", DN@"n"],-Identity[Dta][DN["m"], UP["b"]] Identity[Dta][DN["n"], UP["a"]] +
    Identity[Dta][DN["m"], UP["a"]] Identity[Dta][DN["n"], UP["b"]], "DtaGen"]

(* ::Subsection:: *)
(* LeviCivita *)

DeclareIdx[{u3,d3}, 3, LatinIdx, Brown]
test[LeviCivita[u3@"a", u3@"b", u3@"c"] LeviCivita[d3@"d", d3@"e", d3@"f"], -Identity[Dta][d3["d"], u3["c"]] Identity[Dta][d3["e"], u3["b"]] Identity[Dta][
  d3["f"], u3["a"]] +
    Identity[Dta][d3["d"], u3["b"]] Identity[Dta][d3["e"], u3["c"]] Identity[Dta][
      d3["f"], u3["a"]] +
    Identity[Dta][d3["d"], u3["c"]] Identity[Dta][d3["e"], u3["a"]] Identity[Dta][
      d3["f"], u3["b"]] -
    Identity[Dta][d3["d"], u3["a"]] Identity[Dta][d3["e"], u3["c"]] Identity[Dta][
      d3["f"], u3["b"]] -
    Identity[Dta][d3["d"], u3["b"]] Identity[Dta][d3["e"], u3["a"]] Identity[Dta][
      d3["f"], u3["c"]] +
    Identity[Dta][d3["d"], u3["a"]] Identity[Dta][d3["e"], u3["b"]] Identity[Dta][
      d3["f"], u3["c"]], "2 LeviCivita's"]
test[LeviCivita[u3@"a", u3@"b", u3@"c"] LeviCivita[d3@"a", d3@"d", d3@"e"], -Identity[Dta][d3["d"], u3["c"]] Identity[Dta][d3["e"], u3["b"]] +
    Identity[Dta][d3["d"], u3["b"]] Identity[Dta][d3["e"], u3["c"]], "LeviCivita contract 1"]
test[LeviCivita[u3@"a", u3@"b", u3@"c"] LeviCivita[d3@"a", d3@"b", d3@"d"], 2 Identity[Dta][d3["d"], u3["c"]], "LeviCivita contract 2"]
test[LeviCivita[u3@"a", u3@"b", u3@"c"] LeviCivita[d3@"a", d3@"b", d3@"c"], 6, "LeviCivita contract 3"]

UseMetric[g3, {u3,d3}]
test[LeviCivita[u3@"a", u3@"b", u3@"c"] LeviCivita[u3@"d", u3@"e", u3@"f"], -(g3[u3["a"], u3["f"]]*g3[u3["b"], u3["e"]]*g3[u3["c"], u3["d"]]) + g3[u3["a"], u3["e"]]*g3[u3["b"], u3["f"]]*g3[u3["c"], u3["d"]] + g3[u3["a"], u3["f"]]*g3[u3["b"], u3["d"]]*g3[u3["c"], u3["e"]] - g3[u3["a"], u3["d"]]*g3[u3["b"], u3["f"]]*g3[u3["c"], u3["e"]] - g3[u3["a"], u3["e"]]*g3[u3["b"], u3["d"]]*g3[u3["c"], u3["f"]] + g3[u3["a"], u3["d"]]*g3[u3["b"], u3["e"]]*g3[u3["c"], u3["f"]], "LeviCivita up up"]

(* ::Subsection:: *)
(* Sym, Asym *)

test[Sym[f[d@"a",d@"b"]],f[d@"a",d@"b"]+f[d@"b",d@"a"], "Sym"]
test[AntiSym[f[d@"a",d@"b"]],f[d@"a",d@"b"]-f[d@"b",d@"a"], "AntiSym"]

(* ::Subsection:: *)
(* Pd *)

test[Pd[Dta[u@"a", d@"b"], d@"c"]==0 && Pd[Sin[1], d@"c"]==0&& Pd[dimTest, d@"c"]==0,
  True, "Pd on constants"]
test[Pd[f[u@"a"]g+h[u@"a"], d@"b"],
  Pd[f[u@"a"], d@"b"]g+f[u@"a"]Pd[g, d@"b"]+Pd[h[u@"a"], d@"b"], "Pd add and times"]
test[Pd[undefined, d@"x"], Pd[undefined, d@"x"], "PD on unknown var"]
test[Pd[a_,d@b_]:>f[a,b],Pd[a_,d@b_]:>f[a,b], "Pattern is not considered as background or constant"]

(* ::Subsection:: *)
(* Pm2 *)
test[x Pm2[(a + b)^2, DN] // Simp, x*Pm2[a^2, DN] + 2*x*Pm2[a*b, DN] + x*Pm2[b^2, DN], "Pm2 expand"]
test[PdT[f0test, PdVars[_DN, ___]] := 0; Pm2[f0test g, DN], f0test*Pm2[g, DN], "Pm2 constant"]
test[Pd[Pm2[PdT[f[DN@"a"], PdVars[DN@"b", DE@0]], DN], DN@"b"], PdT[f[DN["a"]], PdVars[DE[0]]], "Pm2 on Pd2"]
(* ::Subsection:: *)
(* Simp Fast *)

test[Simp[f[u@"x", d@"b"] f1[d@"b"], "Method"->"Fast"], f[u["x"], d["a"]] f1[d["a"]], "SimpF re-arrange idx"]

(* ::Subsection:: *)
(* Simp on patterns *)
(* note: patterns can only be on free indices *)
test[Simp[f[DN@a_,DN@c_]x[UP@d_,UP@b_]], f[DN@a_,DN@c_]x[UP@d_,UP@b_], "Simp with patterns"]

(* ::Subsection:: *)
(* DeclareSym *)

test[DeclareSym[fTmp, {UP, UP, DE@0, DN, DN}, Symmetric[{1, 2}]], {Symmetric[{1, 2}]}, "DeclareSym"]
test[DeclareSym[fTmp, {UP, UP, DE@0, DN, DN}, Symmetric[{3, 4}]], {Symmetric[{1, 2}], Symmetric[{3, 4}]}, "DeclareSym combination"]

DeclareSym[fTmp, {UP, UP, DE@0, UP, UP}, Symmetric[{1, 2, 3, 4}]]
test[Attributes[fTmp], {Orderless}, "set orderless for symmetric All"]
test[DeleteSym[fTmp, {UP, UP, DE@0, UP, UP}], Null, "DeleteSym"]
test[Attributes[fTmp], {}, "remove orderless for symmetric All"]

(* ::Subsection:: *)
(* Simp *)
DeclareSym[f3, {DN, DN, DN, DN}, Symmetric[{1, 2}]];
DeclareSym[f3, {DN, DN, DN, DN}, Antisymmetric[{3, 4}]];
test[f3[DN@"i", DN@"j", DN@"i", DN@"j"] // Simp, 0, TestID -> "SimpM symmetric"]
test[Pd[f3[DN@"i", DN@"j", DN@"i", DN@"j"], DN@"k"] // Simp, 0, TestID -> "SimpM antisymmetric"]

test[Pd[f3[d@"i", DE@0, d@"i", DE@0],d@"k"] // Simp, Pd[f3[d["a"], DE[0], d["a"], DE[0]], d["k"]], "SimpM with explicit idx"]
test[c[D2@"b", D2@"c", U2@"a"] A[U2@"b", DN@"\[Mu]"] A[U2@"c",DN@"\[Nu]"] // Simp,
  A[U2["b"], DN["\[Mu]"]] A[U2["c"], DN["\[Nu]"]] c[D2["b"], D2["c"], U2["a"]], "Simp with free idx sorted"]

(*test[Exp[1+ff[DN@"a"] gg[DN@"a"]]//Simp, Exp[1+ff[DN@"a0"] gg[DN@"a0"]], "Simp through Exp"]*)
(*test[Sqrt[1+ff[DN@"a"] gg[DN@"a"]]//Simp, Sqrt[1+ff[DN@"a0"] gg[DN@"a0"]], "Simp through Power"]*)
test[(Series[(1+Eps xx)(1+Eps yy)(1+Eps zz)ff[DN@"a"], {Eps,0,1}]//Simp//Normal)/.Eps->1, (1+xx+yy+zz)ff[DN@"a"]//Expand, "Simp through SeriesData"]

test[a^2 (f[UP@"a"]^4 + 1) // Simp, a^2 + a^2 f[UP["a"]]^2 f[UP["b"]]^2, "Simp with higher than standard powers"]

(* ::Subsection:: *)
(* private functions in tensor.m and util.m *)

<<"MathGR/utilPrivate.m"
test[plus2list[1+a+c], {1, a, c}, "plus2list"]
test[expand2list[1+2(a+c)], {1, 2a, 2c}, "expand2list"]
test[apply2term[testf, 1+2(a+c)], testf[1]+testf[2a]+testf[2c], "apply2term"]
test[getSampleTerm[2(a+c)], 2a, "getSampleTerm"]
test[times2prod[a+b^3 c+d^n], a+prod[b,b,b,c]+d^n, "times2prod"]
test[prod2times[a+prod[b,b,b,c]+d^n], a+b^3 c+d^n, "prod2times"]
test[f[a,b,c]/.{a,b,c}~replaceTo~{x,y,z}, f[x,y,z], "replaceTo"]

test[MathGR`tensor`Private`idx[a[u@"a", d@"b"]Pd[f[u@"c",u@"b"],d@"a"]], {"a","b","c","b","a"}, "idx"]
test[MathGR`tensor`Private`idx[a[u@"a", d@"b"]Pd[f[u@"c",u@"b"],d@"a"]f[d@"x"]^2], {"a","b","x","x","c","b","a"}, "idx2"]
test[MathGR`tensor`Private`free[a[u@"a", d@"b"]Pd[f[u@"c",u@"b"],d@"a"]f[d@"x"]^2], {"c"}, "free"]
test[MathGR`tensor`Private`dummy[a[u@"a", d@"b"]Pd[f[u@"c",u@"b"],d@"a"]f[d@"x"]^2], {"a","b","x"}, "dummy"]
test[MathGR`tensor`Private`pd2pdts[Pd[f[u@"a"],d@"a"]], MathGR`tensor`Private`pdts[1][f][u@"a", d@"a"], "Pd to pdts"]
test[MathGR`tensor`Private`pdts2pd[MathGR`tensor`Private`pdts[1][f][u@"a", d@"a"]], Pd[f[u@"a"],d@"a"], "pdts to Pd"]

test[MathGR`tensor`Private`rmE[{UE@0,u@"a",d@"b",DE@1,d@"c"}], {u@"a",d@"b",d@"c"}, "rmE"]

(* ::Section:: *)
(* Tests for gr.m *)

UseMetric[g, {u,d}]

(* ::Subsection:: *)
(* MetricContract *)

test[MetricContract[f[UG@1, DG@2]f1[UG@1, DG@2]] // Simp,
  f[u["a"], d["b"]]*f1[u["c"], d["d"]]*g[d["a"], d["c"]]*g[u["b"], u["d"]], "MetricContract"]

(* ::Subsection:: *)
(* Affine and curvature *)

test[Affine[u@"a",d@"b",d@"c"]//Simp,
  -(g[u["a"], u["d"]]*Pd[g[d["b"], d["c"]], d["d"]])/2 + (g[u["a"], u["d"]]*Pd[g[d["b"], d["d"]], d["c"]])/2 + (g[u["a"], u["d"]]*Pd[g[d["c"], d["d"]], d["b"]])/2,
  "Affine"]
test[R[]//Simp,
  (3*g[u["a"], u["b"]]*g[u["c"], u["d"]]*g[u["e"], u["f"]]*Pd[g[d["a"], d["c"]], d["e"]]*Pd[g[d["b"], d["d"]], d["f"]])/4 - (g[u["a"], u["b"]]*g[u["c"], u["d"]]*g[u["e"], u["f"]]*Pd[g[d["a"], d["c"]], d["f"]]*Pd[g[d["b"], d["e"]], d["d"]])/2 - g[u["a"], u["b"]]*g[u["c"], u["d"]]*g[u["e"], u["f"]]*Pd[g[d["a"], d["c"]], d["d"]]*Pd[g[d["b"], d["e"]], d["f"]] - (g[u["a"], u["b"]]*g[u["c"], u["d"]]*g[u["e"], u["f"]]*Pd[g[d["a"], d["b"]], d["e"]]*Pd[g[d["c"], d["d"]], d["f"]])/4 + g[u["a"], u["b"]]*g[u["c"], u["d"]]*g[u["e"], u["f"]]*Pd[g[d["a"], d["b"]], d["d"]]*Pd[g[d["c"], d["e"]], d["f"]] - g[u["a"], u["b"]]*g[u["c"], u["d"]]*Pd[Pd[g[d["a"], d["b"]], d["c"]], d["d"]] + g[u["a"], u["b"]]*g[u["c"], u["d"]]*Pd[Pd[g[d["a"], d["c"]], d["b"]], d["d"]],
  "Ricci scalar"]

test[CovD[R[d@"a", d@"b", d@"c", d@"d"], d@"e"] + CovD[R[d@"a", d@"b", d@"d", d@"e"], d@"c"] + CovD[R[d@"a", d@"b", d@"e", d@"c"], d@"d"]// Simp, 0, "Second Bianchi of Riemann"]

(* ::Subsection:: *)
(* CovD *)

test[CovD[f2 f[u@"a",d@"b"]f1[d@"c"] ,d@"d"]//Simp,
  f[u["a"], d["b"]]*f1[d["c"]]*Pd[f2, d["d"]] + f2*f1[d["c"]]*Pd[f[u["a"], d["b"]], d["d"]] + f2*f[u["a"], d["b"]]*Pd[f1[d["c"]], d["d"]] + (f2*f[u["a"], d["e"]]*f1[d["c"]]*g[u["e"], u["f"]]*Pd[g[d["b"], d["d"]], d["f"]])/2 - (f2*f[u["a"], d["e"]]*f1[d["c"]]*g[u["e"], u["f"]]*Pd[g[d["b"], d["f"]], d["d"]])/2 + (f2*f[u["a"], d["b"]]*f1[d["e"]]*g[u["e"], u["f"]]*Pd[g[d["c"], d["d"]], d["f"]])/2 - (f2*f[u["a"], d["b"]]*f1[d["e"]]*g[u["e"], u["f"]]*Pd[g[d["c"], d["f"]], d["d"]])/2 - (f2*f[u["e"], d["b"]]*f1[d["c"]]*g[u["a"], u["f"]]*Pd[g[d["d"], d["e"]], d["f"]])/2 - (f2*f[u["a"], d["e"]]*f1[d["c"]]*g[u["e"], u["f"]]*Pd[g[d["d"], d["f"]], d["b"]])/2 - (f2*f[u["a"], d["b"]]*f1[d["e"]]*g[u["e"], u["f"]]*Pd[g[d["d"], d["f"]], d["c"]])/2 + (f2*f[u["e"], d["b"]]*f1[d["c"]]*g[u["a"], u["f"]]*Pd[g[d["d"], d["f"]], d["e"]])/2 + (f2*f[u["e"], d["b"]]*f1[d["c"]]*g[u["a"], u["f"]]*Pd[g[d["e"], d["f"]], d["d"]])/2,
  "CovD"]

(* ::Section:: *)
(* Tests for ibp.m *)

test[Ibp[y Pd[x, d@"a"] + x Pd[y, d@"a"] + f[d@"a"] + xx yy Pd[zz, d@"a"] +   xx zz Pd[yy, d@"a"] + xxx Pd[yyy, d@"a"]],
  f[d@"a"] - yy zz Pd[xx, d["a"]] + xxx Pd[yyy, d["a"]] +  PdHold[x y, d["a"]] + PdHold[xx yy zz, d["a"]], "Ibp CountLeaf"]

test[Ibp[y Pd[Pd[x, DE@0], DE@0], "Rank"->IbpCountPt2], -Pd[x, DE[0]] Pd[y, DE[0]] + PdHold[y Pd[x, DE[0]], DE[0]], "Ibp CountPt2"]

test[Ibp[y Pd[x, d@"i"], "Rank"->IbpVar[x]], -x Pd[y, d["i"]] + PdHold[x y, d["i"]], "IbpVar"]

test[f Pm2[g, DN] - g Pm2[f, DN] // Ibp , 0, "Ibp on Pm2, rule 1"]

test[Pm2[g*PdT[f, PdVars[DE[0], DN["i"], DN["i"]]], DN] + 2*Pm2[PdT[f, PdVars[DE[0], DN["i"]]]*PdT[g, PdVars[DN["i"]]], DN]//Ibp, g*PdT[f, PdVars[DE[0]]] - Pm2[PdT[f, PdVars[DE[0]]]*PdT[g, PdVars[DN["a"], DN["a"]]], DN], "Ibp on Pm2, rule 2"]

(* ::Section:: *)
(* Tests for decomp.m *)

test[Sqrt[1 + f[DTot@"a"] f[UTot@"a"]] // Decomp0i, Sqrt[1 + f[DE[0]]*f[UE[0]] + f[DN["a"]]*f[UP["a"]]], "Decomp0i in sqrt"];
test[fx[DTot@"A", UTot@"A"] - 1/(1 + f[DTot@"A", UTot@"A"]) // Decomp0i, -(1 + f[DE[0], UE[0]] + f[DN["A"], UP["A"]])^(-1) + fx[DE[0], UE[0]] + fx[DN["A"], UP["A"]], "Decomp0i ordinary term and power"];


(* ::Section:: *)
(* Tests for util.m *)

test[LocalToK[2 x PdT[y, PdVars[DN@"a", DN@"b"]]], 2*x[k[1]]*y[k[2]]*k[2][DN["a"]]*k[2][DN["b"]], "LocalToK"];

(* ::Section:: *)
(* Cosmic perturbations *)
Remove[a,b,h,f]
Get["MathGR/util.m"]
Get["MathGR/ibp.m"]
Get["MathGR/frwadm.m"]
DeclareIdx[{UP, DN}, DefaultDim, LatinIdx, Black]
PdHold[__] := 0
phi = phi0
Evaluate[Pd[phi0, DN@_]] := 0
s012 = Sqrtg (RADM[]/2 + Simp@DecompG2H[X[phi]] - V[phi] ) // SS[2]
Print["Result of s012 =========="];Print[s012]
s1 = s012 // OO[1]
Print["Result of s1 =========="];Print[s1]
SimpHook =  SimpHook~Union~(SolveExpr[{D[s1, \[Alpha]] == 0, D[Ibp[s1, "Rank"->IbpVar[\[Zeta]]], \[Zeta]] == 0}, {V[phi0], Pd[phi0, DE@0]^2}][[1]])
s2 = s012 // OO[2] // Fourier2 // Ibp
Print["Result of s2 =========="];Print[s2]
solCons =  Solve[{D[s2, \[Alpha]] == 0, D[s2, \[Beta]] == 0, D[s2, b[DN@"a"]] == 0}, {\[Alpha], \[Beta], b[DN@"a"]}][[1]]
s2Solved = s2 /. solCons // Ibp[#, "Rank"->IbpStd2] &
Print["Result of s2Solved =========="];Print[s2Solved]
test[s2Solved, -(a*k^2*\[Epsilon]*\[Zeta]^2) + a^3*\[Epsilon]*Pd[\[Zeta], DE[0]]^2, "zeta gauge 2nd order action"]
PdHold[__]=.

(* ::Section:: *)
(* Decomposition *)

test[Sqrt[f1[DTot["b"]]*f2[DTot["b"]]]//Decomp0i, Sqrt[f1[DE[0]]*f2[DE[0]] + f1[DN["b"]]*f2[DN["b"]]], "Decomp0i sqrt"]
test[SeriesData[Eps, 0, {f1[DTot["a"]]*f2[DTot["a"]], Sqrt[f1[DTot["b"]]*f2[DTot["b"]]]}, 1, 3, 1]//Decomp0i,
 SeriesData[Eps, 0, {f1[DE[0]]*f2[DE[0]] + f1[DN["a"]]*f2[DN["a"]], Sqrt[f1[DE[0]]*f2[DE[0]] + f1[DN["b"]]*f2[DN["b"]]]}, 1, 3, 1], "Decomp0i Series" ]

UseMetric[\[DoubleStruckG], {UTot, DTot}]
UseMetric[\[Eta], {U1, D1}, "SetAsDefault" -> False]
UseMetric[\[Gamma], {U2, D2}, "SetAsDefault" -> False]

test[\[DoubleStruckG][U1@"a",D1@"b"], Dta[U1@"a",D1@"b"], "metric on other dual pairs of indices"]
test[\[DoubleStruckG][UTot@"a",D1@"b"], \[DoubleStruckG][UTot@"a",D1@"b"], "metric on non-dual pairs of indices is unevaluated"]

DecompHook={\[DoubleStruckG][D1[\[Alpha]_], D1[\[Beta]_]] :> (\[Eta][Sequence[D1[\[Alpha]], D1[\[Beta]]]] + A[Sequence[U2[#1], D1[\[Alpha]]]]*
    A[Sequence[U2[#1], D1[\[Beta]]]] & )[Uq[1]], \[DoubleStruckG][D1[\[Alpha]_], D2[b_]] :> A[Sequence[U2[b], D1[\[Alpha]]]],
  \[DoubleStruckG][U1[\[Alpha]_], U1[\[Beta]_]] :> \[Eta][Sequence[U1[\[Alpha]], U1[\[Beta]]]],
  \[DoubleStruckG][U1[\[Alpha]_], U2[b_]] :> ((-\[Eta][Sequence[U1[\[Alpha]], U1[#1]]])*A[Sequence[U2[b], D1[#1]]] & )[Uq[1]],
  \[DoubleStruckG][U2[a_], U2[b_]] :> (Dta[Sequence[U2[a], U2[b]]] + \[Eta][Sequence[U1[#1], U1[#2]]]*
      A[Sequence[U2[a], D1[#1]]]*A[Sequence[U2[b], D1[#2]]] & )[Uq[2]],
  \[DoubleStruckG][D2[a_], D2[b_]] :> Dta[Sequence[U2[a], U2[b]]]}

Evaluate[Pd[\[Eta][__], _]] := 0;
Evaluate[Pd[\[Gamma][__], _]] := 0;
Evaluate[Pd[A[__], _D2]] := 0;
Evaluate[Pd[Pd[A[__], _], _D2]] := 0;

R\[Bullet]decomp = DecompSe[R[] // Simp]//Simp

test[TrySimp[R\[Bullet]decomp, (a_.) + (b_.)*Pd[A[U2[m_], D1[\[Alpha]_]], D1[\[Beta]_]] :>
    a + Simp[b*(F[Sequence[U2[m], D1[\[Alpha]], D1[\[Beta]]]] + Pd[A[Sequence[U2[m], D1[\[Beta]]]], D1[\[Alpha]]])]],
  -(F[U2["a"], D1["\[Alpha]"], D1["\[Beta]"]]*Pd[A[U2["a"], D1["\[Gamma]"]], D1["\[Delta]"]]*\[Eta][U1["\[Alpha]"], U1["\[Gamma]"]]*
      \[Eta][U1["\[Beta]"], U1["\[Delta]"]])/2, "Decomposition of non-diag metric into Maxwell"]

(* Generate report *)
testReport[]
Print["Total time used:", OutputForm[SessionTime[]-startTestTime]]
Close[streamMsg];
