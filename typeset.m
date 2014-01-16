(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`typeset`", {"MathGR`tensor`"}]
Begin["`Private`"]

altUp:= Alternatives @@ IdxUpList
altDn:= Alternatives @@ IdxDnList
idxQ[idx__]:= MatchQ[{idx}, {(IdxPtn | IdxNonSumPtn) ..}]

makeBoxesTsrQ = !MatchQ[#, List|Rule|Alternatives|Sequence]&
MakeBoxes[tsr_[idx__], StandardForm]/;(idxQ[idx]&&makeBoxesTsrQ[tsr]):= TagBox[RowBox[{AdjustmentBox[MakeBoxes[tsr, StandardForm], BoxMargins -> {{0, -0.2}, {0, 0}}], 
	StyleBox[ GridBox[{idx} /. {
		{(a:altUp)[i_]:>TagBox[StyleBox[MakeBoxes[i, StandardForm], FontColor->IdxColor@a], a], 
			IdxDnPtn:>"", UE@n_:>TagBox[StyleBox[MakeBoxes[n, StandardForm], FontColor->IdxColor@UE],UE], DE@n_:>""}, 
		{IdxUpPtn:>"", (a:altDn)[i_]:>TagBox[StyleBox[MakeBoxes[i, StandardForm], FontColor->IdxColor@a], a], 
			DE@n_:>TagBox[StyleBox[MakeBoxes[n, StandardForm], FontColor->IdxColor@DE],DE], UE@n_:>""}
	}, ColumnSpacings->0, RowSpacings->0], FontSize->10]}], "mgrTsr"]

parseUD[lst_, StandardForm]:= Sequence @@ (Map[If[#[[1]] === "", #[[2]], #[[1]]] &, Transpose[lst]] /. {TagBox[i_ | StyleBox[i_, __], tag_] :> tag@ToExpression[i, StandardForm]})
MakeExpression[TagBox[RowBox[{AdjustmentBox[t_, ___], StyleBox[GridBox[idx__, ___], ___]}], "mgrTsr"], StandardForm] := 
	With[{h = ToExpression[t, StandardForm], i = parseUD[idx, StandardForm]}, HoldComplete@h@i]

MakeBoxes[PdT[f_, PdVars[i__]], StandardForm]/;FreeQ[{i},DE@0]:= TagBox[RowBox[{Sequence@@(MakeBoxes[\[CapitalSampi]@#, StandardForm]&/@{i}), MakeBoxes[f, StandardForm]}], "mgrPdT"]
MakeExpression[TagBox[RowBox[{d__,f_}], "mgrPdT"], StandardForm]:= 
	With[{idExpr=PdVars@@Cases[ToExpression[{d}, StandardForm], \[CapitalSampi][a_]:>a], fExpr=ToExpression[f, StandardForm]}, HoldComplete@PdT[fExpr, idExpr]]

MakeBoxes[PdT[a_, PdVars[DE@0, i___]], StandardForm]/;FreeQ[{i},DE@0] := With[{h=PdT[a, PdVars[i]]}, OverscriptBox[MakeBoxes[h, StandardForm], "\[Bullet]"]];
MakeBoxes[PdT[a_, PdVars[DE@0, DE@0, i___]], StandardForm]/;FreeQ[{i},DE@0] := With[{h=PdT[a, PdVars[i]]}, OverscriptBox[MakeBoxes[h, StandardForm], "\[Bullet]\[Bullet]"]];
MakeBoxes[PdT[a_, PdVars[DE@0, DE@0, DE@0, i___]], StandardForm]/;FreeQ[{i},DE@0] := With[{h=PdT[a, PdVars[i]]}, OverscriptBox[MakeBoxes[h, StandardForm], "\[Bullet]\[Bullet]\[Bullet]"]];
MakeBoxes[PdT[a_, PdVars[DE@0, DE@0, DE@0, DE@0, i___]], StandardForm] := With[{h=PdT[a, PdVars[i]]}, OverscriptBox[MakeBoxes[h, StandardForm], "\[Bullet]\[Bullet]\[Bullet]\[Bullet]"]];

MakeExpression[OverscriptBox[a_, "\[Bullet]"], StandardForm] := MakeExpression[RowBox[{"Pd[#,DE@0]&@", a}], StandardForm]
MakeExpression[OverscriptBox[a_, "\[Bullet]\[Bullet]"], StandardForm] := MakeExpression[RowBox[{"Pd[#,DE@0]&@Pd[#,DE@0]&@", a}], StandardForm]
MakeExpression[OverscriptBox[a_, "\[Bullet]\[Bullet]\[Bullet]"], StandardForm] := MakeExpression[RowBox[{"Pd[#,DE@0]&@Pd[#,DE@0]&@Pd[#,DE@0]&@", a}], StandardForm]
MakeExpression[OverscriptBox[a_, "\[Bullet]\[Bullet]\[Bullet]\[Bullet]"], StandardForm] := MakeExpression[RowBox[{"Pd[#,DE@0]&@Pd[#,DE@0]&@Pd[#,DE@0]&@Pd[#,DE@0]&@", a}], StandardForm]


(* the following are used for backwards compatibility *)
MakeExpression[TagBox[RowBox[{SubscriptBox["\[CapitalSampi]", a_], f_}], "mgrPd"], StandardForm] := MakeExpression[RowBox[{"Pd[", f, ",", a, "]"}], StandardForm]

(* ::Section:: *)
(* Paste the blob calculated in InputAliases.nb *)

aliasesList= {"tp" -> TagBox[
   RowBox[{SubscriptBox["\[CapitalSampi]", 
      TagBox[StyleBox["\"\[SelectionPlaceholder]\"", 
        FontColor -> GrayLevel[0]], DN]], "\[Placeholder]"}], 
   "mgrPd"], 
 "tp1" -> TagBox[
   RowBox[{SubscriptBox["\[CapitalSampi]", 
      TagBox[StyleBox["\"\[SelectionPlaceholder]\"", 
        FontColor -> GrayLevel[0]], D1]], "\[Placeholder]"}], 
   "mgrPd"], 
 "tp2" -> TagBox[
   RowBox[{SubscriptBox["\[CapitalSampi]", 
      TagBox[StyleBox["\"\[SelectionPlaceholder]\"", 
        FontColor -> RGBColor[1, 0, 0]], D2]], "\[Placeholder]"}], 
   "mgrPd"], 
 "tpt" -> TagBox[
   RowBox[{SubscriptBox["\[CapitalSampi]", 
      TagBox[StyleBox["\"\[SelectionPlaceholder]\"", 
        FontColor -> RGBColor[0, 0, 1]], DTot]], "\[Placeholder]"}], 
   "mgrPd"], 
 "tu" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          UP]}, {""}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "td" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{""}, {TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          DN]}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "tuu" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          UP], TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          UP]}, {"", ""}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "tud" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          UP], ""}, {"", 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> GrayLevel[0]], DN]}}, ColumnSpacings -> 0, 
       RowSpacings -> 0], FontSize -> 10]}], "mgrTsr"], 
 "tdu" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{"", 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> GrayLevel[0]], UP]}, {TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          DN], ""}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "tdd" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{"", 
         ""}, {TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          DN], TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          DN]}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "tuuu" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          UP], 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> GrayLevel[0]], UP], 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> GrayLevel[0]], UP]}, {"", "", ""}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "tudd" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          UP], "", ""}, {"", 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> GrayLevel[0]], DN], 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> GrayLevel[0]], DN]}}, ColumnSpacings -> 0, 
       RowSpacings -> 0], FontSize -> 10]}], "mgrTsr"], 
 "tddd" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{"", "", 
         ""}, {TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          DN], TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          DN], 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> GrayLevel[0]], DN]}}, ColumnSpacings -> 0, 
       RowSpacings -> 0], FontSize -> 10]}], "mgrTsr"], 
 "tuuuu" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          UP], TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          UP], TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          UP], TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          UP]}, {"", "", "", ""}}, ColumnSpacings -> 0, 
       RowSpacings -> 0], FontSize -> 10]}], "mgrTsr"], 
 "tdddd" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{"", "", "", 
         ""}, {TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          DN], TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          DN], 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> GrayLevel[0]], DN], 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> GrayLevel[0]], DN]}}, ColumnSpacings -> 0, 
       RowSpacings -> 0], FontSize -> 10]}], "mgrTsr"], 
 "tu1" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          U1]}, {""}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "td1" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{""}, {TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          D1]}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "tu1u1" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          U1], 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> GrayLevel[0]], U1]}, {"", ""}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "tu1d1" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          U1], ""}, {"", 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> GrayLevel[0]], D1]}}, ColumnSpacings -> 0, 
       RowSpacings -> 0], FontSize -> 10]}], "mgrTsr"], 
 "td1u1" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{"", 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> GrayLevel[0]], U1]}, {TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          D1], ""}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "td1d1" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{"", 
         ""}, {TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          D1], TagBox[
          StyleBox["\"\[Placeholder]\"", FontColor -> GrayLevel[0]], 
          D1]}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "tu2" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[1, 0, 0]], U2]}, {""}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "td2" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{""}, {TagBox[
          StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[1, 0, 0]], D2]}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "tu2u2" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[1, 0, 0]], U2], 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[1, 0, 0]], U2]}, {"", ""}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "tu2d2" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[1, 0, 0]], U2], ""}, {"", 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[1, 0, 0]], D2]}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "td2u2" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{"", 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[1, 0, 0]], U2]}, {TagBox[
          StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[1, 0, 0]], D2], ""}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "td2d2" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{"", 
         ""}, {TagBox[
          StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[1, 0, 0]], D2], 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[1, 0, 0]], D2]}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "tut" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[0, 0, 1]], UTot]}, {""}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "tdt" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{""}, {TagBox[
          StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[0, 0, 1]], DTot]}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "tutut" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[0, 0, 1]], UTot], 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[0, 0, 1]], UTot]}, {"", ""}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "tutdt" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[0, 0, 1]], UTot], ""}, {"", 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[0, 0, 1]], DTot]}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "tdtut" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{"", 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[0, 0, 1]], UTot]}, {TagBox[
          StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[0, 0, 1]], DTot], ""}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "tdtdt" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{"", 
         ""}, {TagBox[
          StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[0, 0, 1]], DTot], 
         TagBox[StyleBox["\"\[Placeholder]\"", 
           FontColor -> RGBColor[0, 0, 1]], DTot]}}, 
       ColumnSpacings -> 0, RowSpacings -> 0], FontSize -> 10]}], 
   "mgrTsr"], 
 "tue" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\[Placeholder]", FontColor -> GrayLevel[0.5]], 
          UE]}, {""}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "tde" -> TagBox[
   RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{""}, {TagBox[
          StyleBox["\[Placeholder]", FontColor -> GrayLevel[0.5]], 
          DE]}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "tueue" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\[Placeholder]", FontColor -> GrayLevel[0.5]], 
          UE], TagBox[
          StyleBox["\[Placeholder]", FontColor -> GrayLevel[0.5]], 
          UE]}, {"", ""}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "tuede" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{TagBox[
          StyleBox["\[Placeholder]", FontColor -> GrayLevel[0.5]], 
          UE], ""}, {"", 
         TagBox[StyleBox["\[Placeholder]", 
           FontColor -> GrayLevel[0.5]], DE]}}, ColumnSpacings -> 0, 
       RowSpacings -> 0], FontSize -> 10]}], "mgrTsr"], 
 "tdeue" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{"", 
         TagBox[StyleBox["\[Placeholder]", 
           FontColor -> GrayLevel[0.5]], UE]}, {TagBox[
          StyleBox["\[Placeholder]", FontColor -> GrayLevel[0.5]], 
          DE], ""}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"], 
 "tdede" -> 
  TagBox[RowBox[{AdjustmentBox["\[SelectionPlaceholder]", 
      BoxMargins -> {{0, -0.2}, {0, 0}}], 
     StyleBox[
      GridBox[{{"", 
         ""}, {TagBox[
          StyleBox["\[Placeholder]", FontColor -> GrayLevel[0.5]], 
          DE], TagBox[
          StyleBox["\[Placeholder]", FontColor -> GrayLevel[0.5]], 
          DE]}}, ColumnSpacings -> 0, RowSpacings -> 0], 
      FontSize -> 10]}], "mgrTsr"]}

SetOptions[EvaluationNotebook[], InputAliases -> aliasesList];

End[]
EndPackage[]