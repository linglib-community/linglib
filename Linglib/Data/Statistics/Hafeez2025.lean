module

public import Linglib.Data.Statistics.Schema

/-!
# Hafeez2025: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Hafeez2025.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The acceptability rating study (chapter 5) and the discourse production study (chapter 6) of Urdu
causal constructions, run on the 43 video clips of the Causality Across Languages project. Twelve
raters judged a description of each clip in each of seven response types; a conditional inference
tree per response type splits the clips by the semantic predictors, and Table 18 prints each leaf's
share of ceiling ratings and its number of responses. The tables are recorded as printed, including
the reversed InanCEAF signs of the ADV tree, the peaks of NCA and NCrA that Table 19 swaps, and the
unattainable 0.08 of the LEX-INST tree; the studies that consume them state the discrepancies.

## Raw data

* <https://github.com/JuergenBohnemeyer/cal_stats>: the R analyses of the Causality Across Languages
  project, with the project's clip coding in Non_df_input_csvs/ClipVariables.csv, which codes clips
  11 and 21 with a human second participant and clip 22 without one, as the clip names do; the
  rating responses are not included
* <https://github.com/Saima-Hafeez/Agentivity-and-Causation-Hafeez-Sreeram>: the dissertation's R
  code
* <https://causalityacrosslanguages.wordpress.com/project-summary/field-manual-and-stimuli/>: the
  project's field manuals and stimulus clips

## References

* [hafeez-2025]
-/

@[expose] public section

namespace Hafeez2025

open Data.Statistics

/-- The semantic predictors coded for each clip (Table 4, Appendix L). -/
inductive Predictor where
  /-- IHCr: intentional human causer -/
  | ihcr
  /-- NFCr: natural force causer -/
  | nfcr
  /-- AHCr: accidental human causer -/
  | ahcr
  /-- ContrHCEAF: controlling human causee or affectee -/
  | contrHCEAF
  /-- InanCEAF: inanimate causee or affectee -/
  | inanCEAF
  /-- Mediation: a third participant mediates the chain -/
  | mediation
  /-- PhysImpHCEAF: physically impacted human causee or affectee -/
  | physImpHCEAF
  /-- PsychImpHCEAF: psychologically impacted human causee or affectee -/
  | psychImpHCEAF
  deriving DecidableEq, Repr, Fintype

/-- The first letter of a clip name (Appendix L). -/
inductive CauserCode where
  /-- H: intentional human causer -/
  | h
  /-- U: unintentional causer -/
  | u
  /-- N: natural force causer -/
  | n
  deriving DecidableEq, Repr, Fintype

/-- A later letter of a clip name (Appendix L). -/
inductive ParticipantCode where
  /-- C: controlling human causee or affectee -/
  | c
  /-- U: non-controlling human causee or affectee -/
  | u
  /-- M: physically impacted human causee or affectee, used once for an umbrella -/
  | m
  /-- O: inanimate affectee -/
  | o
  deriving DecidableEq, Repr, Fintype

/-- The response types of the two studies (Appendix L). -/
inductive ResponseType where
  /-- LEX-ERG: lexical ergative construction -/
  | lexErg
  /-- LEX-NOM: lexical nominative construction -/
  | lexNom
  /-- LEX-INST: lexical instrumental construction -/
  | lexInst
  /-- LEX-DAT: lexical dative response type -/
  | lexDat
  /-- MCV: morphological causative construction -/
  | mcv
  /-- ACC: anaphoric causative construction -/
  | acc
  /-- ADV: adverbial causal construction -/
  | adv
  /-- NCrA: non-sentential causer adjunct construction -/
  | ncrA
  /-- NCA: non-sentential cause adjunct construction -/
  | nca
  /-- IMP-CAUS-REL: implicit causal relation construction -/
  | impCausRel
  deriving DecidableEq, Repr, Fintype

/-- A yes-or-no cell of Table 25. -/
inductive Answer where
  /-- Yes: yes -/
  | yes
  /-- No: no -/
  | no
  deriving DecidableEq, Repr, Fintype

/-- The number of participants in the acceptability rating study, each rating every description.
(section 5.1, p. 112; checked against the PDF text layer only.) -/
def raters : ℕ := 12

/-- A row of Tables 3 and 4 (pp. 45-47, 51-52) and Appendix L: a stimulus clip, with the letters
of its name and the predictors Table 4 marks present. -/
structure Clip where
  /-- The clip number, in the first presentation order. -/
  number : ℕ
  /-- The first letter of the clip name. -/
  causer : CauserCode
  /-- The second letter of the clip name. -/
  second : ParticipantCode
  /-- The third letter of the clip name, when it is the O of an inanimate affectee. -/
  third : Option ParticipantCode
  /-- The predictors Table 4 marks Yes. -/
  present : List Predictor
  deriving DecidableEq, Repr

/-- The 43 rows of Tables 3 and 4 (pp. 45-47, 51-52) and Appendix L, in the paper's order; from
an experiment; checked against the page images. -/
def clips : List Clip :=
  [⟨1, .h, .o, none, [.ihcr, .inanCEAF, .psychImpHCEAF]⟩,  -- HO6_paper
   ⟨2, .h, .c, none, [.ihcr, .contrHCEAF]⟩,  -- HC1_leave
   ⟨3, .h, .o, none, [.ihcr, .inanCEAF]⟩,  -- HOIproc1_swing
   ⟨4, .h, .u, some .o, [.ihcr, .mediation, .psychImpHCEAF]⟩,  -- HUO3_paper
   ⟨5, .h, .o, none, [.ihcr, .inanCEAF]⟩,  -- HO2_egg
   ⟨6, .n, .m, none, [.nfcr, .physImpHCEAF]⟩,  -- NM2_reporter
   ⟨7, .h, .o, none, [.ihcr, .inanCEAF]⟩,  -- HOI4_ball
   ⟨8, .h, .o, none, [.ihcr, .inanCEAF]⟩,  -- HO5_cuptower
   ⟨9, .u, .o, none, [.ahcr, .inanCEAF]⟩,  -- UO1_egg
   ⟨10, .u, .m, none, [.ahcr, .physImpHCEAF]⟩,  -- UM3_faint
   ⟨11, .h, .m, some .o, [.ihcr, .inanCEAF, .mediation, .physImpHCEAF]⟩,  -- HMO4_cups
   ⟨12, .h, .u, none, [.ihcr, .psychImpHCEAF]⟩,  -- HU2_scare
   ⟨13, .u, .o, none, [.ahcr, .inanCEAF]⟩,  -- UO2_paper
   ⟨14, .h, .c, some .o, [.ihcr, .contrHCEAF, .mediation]⟩,  -- HCO3_egg_new
   ⟨15, .n, .c, none, [.nfcr, .contrHCEAF]⟩,  -- NC1_tsunami
   ⟨16, .h, .o, none, [.ihcr, .inanCEAF]⟩,  -- HOI3_plate
   ⟨17, .u, .c, none, [.ahcr, .contrHCEAF]⟩,  -- UC1_sing
   ⟨18, .h, .c, some .o, [.ihcr, .contrHCEAF, .mediation]⟩,  -- HCOI2_paper
   ⟨19, .h, .o, none, [.ihcr, .inanCEAF]⟩,  -- HO4_ball
   ⟨20, .h, .m, none, [.ihcr, .physImpHCEAF]⟩,  -- HM1_fall
   ⟨21, .u, .m, some .o, [.ahcr, .inanCEAF, .mediation, .physImpHCEAF]⟩,  -- UMO2_cups
   ⟨22, .n, .m, none, [.nfcr, .physImpHCEAF]⟩,  -- NM4_umbrella
   ⟨23, .h, .o, none, [.ihcr, .inanCEAF, .physImpHCEAF]⟩,  -- HOI1_paper
   ⟨24, .h, .u, some .o, [.ihcr, .mediation, .psychImpHCEAF]⟩,  -- HUO2_cups
   ⟨25, .u, .m, none, [.ahcr, .physImpHCEAF]⟩,  -- UM1_asleep
   ⟨26, .n, .u, none, [.nfcr, .psychImpHCEAF]⟩,  -- NU1_thunder
   ⟨27, .h, .m, some .o, [.ihcr, .mediation, .physImpHCEAF]⟩,  -- HMO3_paper
   ⟨28, .h, .o, none, [.ihcr, .inanCEAF]⟩,  -- HOproc1_swing
   ⟨29, .h, .c, some .o, [.ihcr, .contrHCEAF, .mediation]⟩,  -- HCO2_paper
   ⟨30, .u, .m, none, [.ahcr, .physImpHCEAF]⟩,  -- UM2_overboard
   ⟨31, .u, .o, none, [.ahcr, .inanCEAF]⟩,  -- UOproc1_swing
   ⟨32, .h, .c, none, [.ihcr, .contrHCEAF]⟩,  -- HC2_sit
   ⟨33, .h, .c, some .o, [.ihcr, .contrHCEAF, .mediation]⟩,  -- HCOproc1_swing
   ⟨34, .u, .o, none, [.ahcr, .inanCEAF]⟩,  -- UOI1_cuptower
   ⟨35, .u, .u, none, [.ahcr, .psychImpHCEAF]⟩,  -- UU2_sneeze
   ⟨36, .h, .u, none, [.ihcr, .psychImpHCEAF]⟩,  -- HU1_laugh_new
   ⟨37, .n, .c, some .o, [.nfcr, .contrHCEAF, .mediation]⟩,  -- NCO1_umbrella
   ⟨38, .h, .c, some .o, [.ihcr, .contrHCEAF, .mediation]⟩,  -- HCOI3_plate
   ⟨39, .u, .o, none, [.ahcr, .inanCEAF]⟩,  -- UO3_ball
   ⟨40, .u, .u, some .o, [.ahcr, .mediation, .psychImpHCEAF]⟩,  -- UUO2_paper
   ⟨41, .h, .c, some .o, [.ihcr, .contrHCEAF, .mediation]⟩,  -- HCO4_ball
   ⟨42, .h, .m, none, [.ihcr, .physImpHCEAF]⟩,  -- HM2_strongman
   ⟨43, .u, .u, none, [.ahcr, .psychImpHCEAF]⟩]  -- UU1_yawn

/-- A row of Table 18 (pp. 143-144): a leaf of a response type's conditional inference tree.
Table 18 prints the response types LEX-ERG and MCV as LEX_ERG and MCV_U. -/
structure Leaf where
  /-- The response type whose tree the leaf belongs to. -/
  responseType : ResponseType
  /-- The leaf's node number in the tree plot. -/
  node : ℕ
  /-- The scene type of the leaf, as printed. -/
  path : List (Predictor × Sign)
  /-- The percentage of the leaf's responses given the ceiling rating. -/
  ceilingPercent : Decimal
  /-- The number of responses in the leaf. -/
  responses : ℕ
  deriving DecidableEq, Repr

/-- The 27 rows of Table 18 (pp. 143-144), in the paper's order; from an experiment; checked
against the page images. -/
def leaves : List Leaf :=
  [⟨.lexErg, 2, [(.ihcr, .minus)], ⟨74, 1⟩, 216⟩,
   ⟨.lexErg, 4, [(.ihcr, .plus), (.mediation, .plus)], ⟨25, 1⟩, 120⟩,
   ⟨.lexErg, 6, [(.ihcr, .plus), (.mediation, .minus), (.inanCEAF, .plus)], ⟨991, 1⟩, 108⟩,
   ⟨.lexErg, 7, [(.ihcr, .plus), (.mediation, .minus), (.inanCEAF, .minus)], ⟨75, 0⟩, 72⟩,
   ⟨.lexInst, 3, [(.ihcr, .plus), (.psychImpHCEAF, .plus)], ⟨167, 1⟩, 48⟩,
   ⟨.lexInst, 4, [(.ihcr, .plus), (.psychImpHCEAF, .minus)], ⟨8, 2⟩, 252⟩,
   ⟨.lexInst, 7, [(.ihcr, .minus), (.contrHCEAF, .minus), (.inanCEAF, .plus)], ⟨875, 1⟩, 72⟩,
   ⟨.lexInst, 8, [(.ihcr, .minus), (.contrHCEAF, .minus), (.inanCEAF, .minus)], ⟨556, 1⟩, 99⟩,
   ⟨.lexInst, 9, [(.ihcr, .minus), (.contrHCEAF, .plus)], ⟨28, 1⟩, 36⟩,
   ⟨.lexDat, 2, [(.contrHCEAF, .plus)], ⟨417, 1⟩, 132⟩,
   ⟨.lexDat, 4, [(.contrHCEAF, .minus), (.nfcr, .plus)], ⟨56, 1⟩, 36⟩,
   ⟨.lexDat, 5, [(.contrHCEAF, .minus), (.nfcr, .minus)], ⟨0, 0⟩, 336⟩,
   ⟨.mcv, 3, [(.mediation, .plus), (.ihcr, .minus)], ⟨222, 1⟩, 36⟩,
   ⟨.mcv, 5, [(.mediation, .plus), (.ihcr, .plus), (.contrHCEAF, .plus)], ⟨931, 1⟩, 72⟩,
   ⟨.mcv, 6, [(.mediation, .plus), (.ihcr, .plus), (.contrHCEAF, .minus)], ⟨583, 1⟩, 48⟩,
   ⟨.mcv, 8, [(.mediation, .minus), (.contrHCEAF, .plus)], ⟨83, 1⟩, 48⟩,
   ⟨.mcv, 9, [(.mediation, .minus), (.contrHCEAF, .minus)], ⟨13, 1⟩, 312⟩,
   ⟨.adv, 3, [(.inanCEAF, .minus), (.ihcr, .plus)], ⟨87, 0⟩, 108⟩,
   ⟨.adv, 4, [(.inanCEAF, .minus), (.ihcr, .minus)], ⟨625, 1⟩, 72⟩,
   ⟨.adv, 5, [(.inanCEAF, .plus)], ⟨908, 1⟩, 336⟩,
   ⟨.nca, 3, [(.inanCEAF, .minus), (.nfcr, .minus)], ⟨951, 1⟩, 288⟩,
   ⟨.nca, 4, [(.inanCEAF, .minus), (.nfcr, .plus)], ⟨833, 1⟩, 48⟩,
   ⟨.nca, 5, [(.inanCEAF, .plus)], ⟨656, 1⟩, 180⟩,
   ⟨.ncrA, 3, [(.inanCEAF, .plus), (.ihcr, .minus)], ⟨681, 1⟩, 72⟩,
   ⟨.ncrA, 4, [(.inanCEAF, .plus), (.ihcr, .plus)], ⟨463, 1⟩, 108⟩,
   ⟨.ncrA, 6, [(.inanCEAF, .minus), (.nfcr, .plus)], ⟨938, 1⟩, 48⟩,
   ⟨.ncrA, 7, [(.inanCEAF, .minus), (.nfcr, .minus)], ⟨746, 1⟩, 252⟩]

/-- A row of Table 19 (pp. 149-150): a response type with its semantic prototype and its
acceptability peak. -/
structure SummaryRow where
  /-- The response type. -/
  responseType : ResponseType
  /-- The semantic prototype; none where the table prints NO. -/
  prototype : Option (List (Predictor × Sign))
  /-- The acceptability percentage printed beside it. -/
  percent : Decimal
  deriving DecidableEq, Repr

/-- The 7 rows of Table 19 (pp. 149-150), in the paper's order; from an experiment; checked
against the page images. -/
def summary : List SummaryRow :=
  [⟨.lexErg, some [(.ihcr, .plus), (.inanCEAF, .plus)], ⟨991, 1⟩⟩,
   ⟨.lexInst,  -- printed [-IHCr, - +InanCEAF]
     some [(.ihcr, .minus), (.inanCEAF, .plus)],
     ⟨875, 1⟩⟩,
   ⟨.lexDat, none, ⟨417, 1⟩⟩,  -- printed NO
   ⟨.mcv, some [(.mediation, .plus), (.ihcr, .plus), (.contrHCEAF, .plus)], ⟨931, 1⟩⟩,
   ⟨.adv, some [(.inanCEAF, .plus)], ⟨908, 1⟩⟩,
   ⟨.ncrA, some [(.inanCEAF, .minus), (.nfcr, .plus)], ⟨951, 1⟩⟩,
   ⟨.nca, some [(.inanCEAF, .minus), (.nfcr, .minus)], ⟨938, 1⟩⟩]

/-- A row of Table 25 (pp. 218-219): a response type's prototype in the acceptability study and
its preferences in the production study. -/
structure ComparisonRow where
  /-- The response type. -/
  responseType : ResponseType
  /-- Whether the acceptability study tested it. -/
  rated : Answer
  /-- Its prototype in the acceptability study; none where the table prints No or N/A. -/
  prototype : Option (List (Predictor × Sign))
  /-- Whether it occurred in the production study. -/
  produced : Answer
  /-- The scene type the model of all response types prefers it for (fifth column). -/
  combinedPreference : Option (List (Predictor × Sign))
  /-- The scene types its own model prefers it for (sixth column). -/
  individualPreferences : List (List (Predictor × Sign))
  deriving DecidableEq, Repr

/-- The 10 rows of Table 25 (pp. 218-219), in the paper's order; from an experiment; checked
against the page images. -/
def comparison : List ComparisonRow :=
  [⟨.lexErg,
     .yes,
     some [(.ihcr, .plus), (.inanCEAF, .plus)],
     .yes,
     some [(.inanCEAF, .plus), (.ihcr, .plus)],
     [[(.inanCEAF, .plus), (.ihcr, .plus)]]⟩,
   ⟨.lexNom, .no, none, .yes, none, []⟩,
   ⟨.lexInst,  -- prototype printed [-IHCr, - +InanCEAF]
     .yes,
     some [(.ihcr, .minus), (.inanCEAF, .plus)],
     .yes,
     none,
     []⟩,
   ⟨.lexDat, .yes, none, .no, none, []⟩,
   ⟨.mcv, .yes, some [(.mediation, .plus), (.ihcr, .plus), (.contrHCEAF, .plus)], .no, none, []⟩,
   ⟨.acc, .no, none, .yes, none, []⟩,
   ⟨.adv, .yes, some [(.inanCEAF, .plus)], .yes, none, []⟩,
   ⟨.ncrA,
     .yes,
     some [(.inanCEAF, .minus), (.nfcr, .plus)],
     .yes,
     some [(.nfcr, .plus), (.physImpHCEAF, .plus)],
     [[(.inanCEAF, .minus), (.nfcr, .plus), (.physImpHCEAF, .plus)]]⟩,
   ⟨.nca,
     .yes,
     some [(.inanCEAF, .minus), (.nfcr, .minus)],
     .yes,
     some [(.psychImpHCEAF, .plus)],
     [[(.nfcr, .minus), (.psychImpHCEAF, .plus)]]⟩,
   ⟨.impCausRel,
     .no,
     none,
     .yes,
     some [(.contrHCEAF, .plus), (.ihcr, .plus)],
     [[(.nfcr, .minus), (.contrHCEAF, .plus)],
      [(.inanCEAF, .plus), (.ihcr, .minus), (.ahcr, .plus)]]⟩]

end Hafeez2025
