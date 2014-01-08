(* Yi Wang, 2013, tririverwangyi@gmail.com, GPLv3 *)
BeginPackage["MathGR`typeset`", {"MathGR`tensor`"}]
Begin["`Private`"]

altUp:= Alternatives @@ IdxUpList
altDn:= Alternatives @@ IdxDnList
idxQ[idx__]:= MatchQ[{idx}, {(IdxPtn | IdxNonSumPtn) ..}]

MakeBoxes[tsr_[idx__], form_]/;(idxQ[idx]&&tsr=!=List&&tsr=!=Rule):= TagBox[RowBox[{AdjustmentBox[MakeBoxes[tsr, form], BoxMargins -> {{0, -0.2}, {0, 0}}], 
	StyleBox[ GridBox[{idx} /. {
		{(a:altUp)[i_]:>TagBox[StyleBox[MakeBoxes[i, form], FontColor->IdxColor@a], a], 
			IdxDnPtn:>"", UE@n_:>TagBox[StyleBox[MakeBoxes[n, form], FontColor->IdxColor@UE],UE], DE@n_:>""}, 
		{IdxUpPtn:>"", (a:altDn)[i_]:>TagBox[StyleBox[MakeBoxes[i, form], FontColor->IdxColor@a], a], 
			DE@n_:>TagBox[StyleBox[MakeBoxes[n, form], FontColor->IdxColor@DE],DE], UE@n_:>""}
	}, ColumnSpacings->0, RowSpacings->0], FontSize->10]}], "mgrTsr"]

parseUD[lst_, form_]:= Sequence @@ (Map[If[#[[1]] === "", #[[2]], #[[1]]] &, Transpose[lst]] /. {TagBox[i_ | StyleBox[i_, __], tag_] :> tag@ToExpression[i, form]})
MakeExpression[TagBox[RowBox[{AdjustmentBox[t_, ___], StyleBox[GridBox[idx__, ___], ___]}], "mgrTsr"], form_] := 
	With[{h = ToExpression[t, form], i = parseUD[idx, form]}, HoldComplete@h@i]
		
MakeBoxes[Pd[f_, d_@i_], form_] /; MatchQ[d, altDn] := TagBox[RowBox[{SubscriptBox["\[CapitalSampi]", 
		TagBox[StyleBox[MakeBoxes[i, form], FontColor -> IdxColor@d], d]], MakeBoxes[f, form]}], "mgrPd"]

MakeExpression[TagBox[RowBox[{SubscriptBox["\[CapitalSampi]", a_], f_}], "mgrPd"], form_] := MakeExpression[RowBox[{"Pd[", f, ",", a, "]"}], form]

(* following: time derivative. May need cleanup *)

MakeBoxes[Pd[a_, DE@0], form_] := OverscriptBox[MakeBoxes[a, form], "\[Bullet]"];
MakeBoxes[Pd[Pd[a_, DE@0], DE@0], form_] := OverscriptBox[MakeBoxes[a, form], "\[Bullet]\[Bullet]"]
MakeBoxes[Pd[Pd[Pd[a_, DE@0], DE@0], DE@0], form_] := OverscriptBox[MakeBoxes[a, form], "\[Bullet]\[Bullet]\[Bullet]"]
MakeBoxes[Pd[Pd[Pd[Pd[a_, DE@0], DE@0], DE@0], DE@0], form_] := OverscriptBox[MakeBoxes[a, form], "\[Bullet]\[Bullet]\[Bullet]\[Bullet]"]

MakeExpression[OverscriptBox[a_, "\[Bullet]"], form_] := MakeExpression[RowBox[{"Pd[#,DE@0]&@", a}], form]
MakeExpression[OverscriptBox[a_, "\[Bullet]\[Bullet]"], form_] := MakeExpression[RowBox[{"Pd[#,DE@0]&@Pd[#,DE@0]&@", a}], form]
MakeExpression[OverscriptBox[a_, "\[Bullet]\[Bullet]\[Bullet]"], form_] := MakeExpression[RowBox[{"Pd[#,DE@0]&@Pd[#,DE@0]&@Pd[#,DE@0]&@", a}], form]
MakeExpression[OverscriptBox[a_, "\[Bullet]\[Bullet]\[Bullet]\[Bullet]"], form_] := MakeExpression[RowBox[{"Pd[#,DE@0]&@Pd[#,DE@0]&@Pd[#,DE@0]&@Pd[#,DE@0]&@", a}], form]


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