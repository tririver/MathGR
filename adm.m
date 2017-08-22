(* ::Package:: *)

(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`adm`", {"MathGR`tensor`", "MathGR`decomp`", "MathGR`gr`", "MathGR`util`", "MathGR`ibp`"}]

DeclareIdx[{UP, DN}, DefaultDim, LatinIdx]
	
SimpHook = {DefaultDim->3}
LapseN = \[ScriptCapitalN]
ShiftN[DN@i_] := \[ScriptCapitalN][DN@i]
Sqrtg:= \[ScriptCapitalN]* Sqrth * a^3
UseMetric[h]

(* 4d metric is used to be decomposed and be replaced. *)
DecompHook = { 
	g[DN@i_, DN@j_]:> h[DN@i, DN@j],
	g[DE@0, DE@0]:> (-\[ScriptCapitalN]^2 + h[UP@#1, UP@#2]ShiftN[DN@#1]ShiftN[DN@#2] &@Uq[2]),
	g[DE@0, DN@i_]:> ShiftN[DN@i],
	g[UP@i_, UP@j_]:> (h[UP@i, UP@j] - ShiftN[DN@#1]ShiftN[DN@#2]h[UP@#1, UP@i]h[UP@#2, UP@j]/\[ScriptCapitalN]^2 &@Uq[2]),
	g[UE@0, UE@0]:> -1/\[ScriptCapitalN]^2,
	g[UE@0, UP@i_]:> (h[UP@i, UP@#]ShiftN[DN@#]/\[ScriptCapitalN]^2 &@Uq[1])}


SetAttributes[DecompG2H, HoldAll]
DecompG2H[f_]:= Decomp0i@WithMetric[g, {UTot, DTot}, MetricContract[f]]


EndPackage[]
