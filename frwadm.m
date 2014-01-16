(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`frwadm`", {"MathGR`tensor`", "MathGR`decomp`", "MathGR`gr`", "MathGR`util`", "MathGR`ibp`"}]

DeclareIdx[{UP, DN}, DefaultDim, LatinIdx]

Pd[Mp,_]:=0
(Pd[#,DN@_]:=0) &/@ {a, H, \[Epsilon], \[Eta]}
SimpHook = {DefaultDim->3, Pd[a, DE@0]->a*H, Pd[H, DE@0]->-\[Epsilon]*H*H, Pd[\[Epsilon], DE@0]->H*\[Epsilon]*\[Eta], Pd[\[Eta], DE@0] -> H*\[Eta]2*\[Eta],
	PdT[H, PdVars[DE@0,DE@0]] -> 2 H^3 \[Epsilon]^2 - H^3 \[Epsilon] \[Eta], PdT[a, PdVars[DE@0,DE@0]] -> a H^2 - a H^2 \[Epsilon]}
LapseN = 1 + Eps * \[Alpha]
ShiftN[DN@i_] := Eps * Pd[\[Beta], DN@i] + Eps * b[DN@i]
Evaluate[Pd[b[DN@i_],DN@i_]]:= 0
b /: b[DN@i_] k[DN@i_]:= 0 (* Above expression in momentum space. *)
Sqrtg:= LapseN*Exp[3*Eps*\[Zeta]] * a^3

UseMetric[h]
h[DN@i_, DN@j_]:= a * a * Exp[2*Eps*\[Zeta]] * Dta[DN@i, DN@j]
h[UP@i_, UP@j_]:= Exp[-2*Eps*\[Zeta]] * Dta[DN@i, DN@j] /a /a

(* 4d metric is used to be decomposed and be replaced. *)
DecompHook = { 
	g[DN@i_, DN@j_]:> h[DN@i, DN@j],
	g[DE@0, DE@0]:> (-LapseN^2 + h[UP@#1, UP@#2]ShiftN[DN@#1]ShiftN[DN@#2] &@Uq[2]),
	g[DE@0, DN@i_]:> ShiftN[DN@i],
	g[UP@i_, UP@j_]:> (h[UP@i, UP@j] - ShiftN[DN@#1]ShiftN[DN@#2]h[UP@#1, UP@i]h[UP@#2, UP@j]/LapseN^2 &@Uq[2]),
	g[UE@0, UE@0]:> -1/LapseN^2,
	g[UE@0, UP@i_]:> (h[UP@i, UP@#]ShiftN[DN@#]/LapseN^2 &@Uq[1])}


SetAttributes[DecompG2H, HoldAll]
DecompG2H[f_]:= Decomp0i@WithMetric[g, {UTot, DTot}, MetricContract[f]]

EndPackage[]