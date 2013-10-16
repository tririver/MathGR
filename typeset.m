(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`look`", {"MathGR`tensor`"}]
Begin["`Private`"]

altUp:= Alternatives @@ IdxUpList
altDn:= Alternatives @@ IdxDnList
idxQ[idx__]:= MatchQ[{idx}, {(IdxPtn | IdxNonSumPtn) ..}]

MakeBoxes[tsr_[idx__], form_]/;(idxQ[idx]&&tsr=!=List):= TagBox[RowBox[{AdjustmentBox[MakeBoxes[tsr, form], BoxMargins -> {{0, -0.2}, {0, 0}}], 
	StyleBox[ GridBox[{idx} /. {
		{(a:altUp)[i_]:>TagBox[StyleBox[MakeBoxes[i, form], FontColor->IdxColor@a], a], 
			IdxDnPtn:>"", UE@n_:>TagBox[StyleBox[MakeBoxes[n, form], FontColor->IdxColor@UE],UE], DE@n_:>""}, 
		{IdxUpPtn:>"", (a:altDn)[i_]:>TagBox[StyleBox[MakeBoxes[i, form], FontColor->IdxColor@a], a], 
			DE@n_:>TagBox[StyleBox[MakeBoxes[n, form], FontColor->IdxColor@DE],DE], UE@n_:>""}
	}, ColumnSpacings->0, RowSpacings->0], FontSize->10]}], "mgrTsr"]

parseUD[lst_]:= (Map[If[#[[1]] === "", #[[2]], #[[1]]] & , Transpose[lst]] 
	/. {TagBox[StyleBox[i_, __], tag_] :> {tag, "[", i, "]"}, TagBox[i_, tag_] :> {tag, "[", i, "]"}})

MakeExpression[TagBox[RowBox[{AdjustmentBox[t_, ___], StyleBox[GridBox[idx__, ___], ___]}], "mgrTsr"], form_] := 
	MakeExpression[RowBox[{t, "[", Sequence @@ Flatten[Riffle[parseUD[idx], ","]], "]"}], form]

MakeBoxes[Pd[f_, d_@i_], form_] /; MatchQ[d, altDn] := TagBox[RowBox[{SubscriptBox["\[CapitalSampi]", 
		TagBox[StyleBox[MakeBoxes[i, form], FontColor -> IdxColor@d], d]], MakeBoxes[f, form]}], "mgrPd"]

MakeExpression[TagBox[RowBox[{SubscriptBox["\[CapitalSampi]", a_], f_}], "mgrPd"], form_] := MakeExpression[RowBox[{"Pd[", f, ",", a, "]"}], form]

End[]
EndPackage[]