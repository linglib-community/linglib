module

public import Linglib.Data.Statistics.Schema

/-!
# Narrog2009: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Narrog2009.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The scopal behavior of the modal markers of Modern Japanese against aspect, negation, tense,
nominalization and illocutionary modulation, from a corpus study.

## References

* [narrog-2009a]
-/

@[expose] public section

namespace Narrog2009

open Data.Statistics

/-- The modal markers of the study, in the order of the table that arranges them by scopal
behavior, narrowest scope first. -/
inductive Marker where
  /-- -Eru: a marker of dynamic modality -/
  | eru
  /-- -(r)areru: a marker of dynamic modality -/
  | rareru
  /-- koto ga dekiru: a marker of dynamic modality -/
  | kotoGaDekiru
  /-- -soo(1): a marker of evidentiality -/
  | soo1
  /-- -tai: a marker of boulomaic modality -/
  | tai
  /-- -Te hosii: a marker of boulomaic modality -/
  | teHosii
  /-- -(a)nakereba naranai: a marker of deontic modality -/
  | nakerebaNaranai
  /-- -(r)eba ii: a marker of deontic modality -/
  | rebaIi
  /-- beki: a marker of deontic modality -/
  | beki
  /-- hazu: a marker of epistemic modality -/
  | hazu
  /-- yoo: a marker of evidentiality -/
  | yoo
  /-- rasii: a marker of evidentiality -/
  | rasii
  /-- ka mo sirenai: a marker of epistemic modality -/
  | kaMoSirenai
  /-- -soo(2): a marker of evidentiality -/
  | soo2
  /-- daroo: a marker of epistemic modality -/
  | daroo
  /-- Hortative -(y)oo: a marker of mood -/
  | hortative
  /-- Imperative I: a marker of mood -/
  | imperativeI
  /-- Imperative II: a marker of mood -/
  | imperativeII
  deriving DecidableEq, Repr, Fintype

/-- The modal categories of the markers. -/
inductive ModalCategory where
  /-- DYN: dynamic modality -/
  | dynamic
  /-- EVI: evidentiality -/
  | evidential
  /-- BOU: boulomaic modality -/
  | boulomaic
  /-- DEO: deontic modality -/
  | deontic
  /-- EPI: epistemic modality -/
  | epistemic
  /-- MOO: mood -/
  | mood
  deriving DecidableEq, Repr, Fintype

/-- The categories the markers are tested against. -/
inductive Category where
  /-- stative aspect: stative aspect -/
  | stativeAspect
  /-- compl. aspect: completive aspect -/
  | completiveAspect
  /-- internal neg: internal negation -/
  | internalNegation
  /-- external neg: external negation -/
  | externalNegation
  /-- tense: past tense -/
  | tense
  /-- nominalization/complementation: nominalization and complementation -/
  | nominalization
  /-- illocutionary modulation: illocutionary modulation -/
  | illocutionaryModulation
  deriving DecidableEq, Repr, Fintype

/-- The scope relation of a marker to a category. -/
inductive Scope where
  /-- ⊂: the marker can be embedded by the category and cannot embed it -/
  | embedded
  /-- ⊂|⊃: the marker can embed the category and be embedded by it -/
  | both
  /-- ⊃: the marker can embed the category and cannot be embedded by it -/
  | embeds
  /-- —: no interaction -/
  | none
  deriving DecidableEq, Repr, Fintype

/-- The tentative layer of a marker from its interaction with other modal markers, the widest
scope last. -/
inductive Layer where
  /-- 4: layer 4 -/
  | l4
  /-- 3b: layer 3b -/
  | l3b
  /-- 3a: layer 3a -/
  | l3a
  /-- 2: layer 2 -/
  | l2
  /-- 1: layer 1 -/
  | l1
  /-- 0: layer 0 -/
  | l0
  deriving DecidableEq, Repr, Fintype

/-- The layer of a marker in non-matrix clauses in the Minami model, the lowest first. -/
inductive ClauseLayer where
  /-- B: layer B -/
  | b
  /-- B~C: layer B~C -/
  | bc
  /-- C: layer C -/
  | c
  /-- C~D: layer C~D -/
  | cd
  /-- D: layer D -/
  | d
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 49, p. 227: a modal marker with its modal category and its layers. -/
structure MarkerRow where
  /-- Its modal category. -/
  category : ModalCategory
  /-- Its layer among the modal markers. -/
  layer : Layer
  /-- Its layer in non-matrix clauses. -/
  clauseLayer : ClauseLayer
  deriving DecidableEq, Repr

/-- The cells of Table 49, p. 227, by marker; counted in a corpus; checked against the page
images. -/
def markers : Marker → MarkerRow
  | .eru => ⟨.dynamic, .l4, .b⟩
  | .rareru => ⟨.dynamic, .l4, .b⟩
  | .kotoGaDekiru => ⟨.dynamic, .l4, .b⟩
  | .soo1 => ⟨.evidential, .l3b, .b⟩
  | .tai => ⟨.boulomaic, .l3b, .b⟩
  | .teHosii => ⟨.boulomaic, .l3b, .b⟩
  | .nakerebaNaranai => ⟨.deontic, .l3b, .b⟩
  | .rebaIi => ⟨.deontic, .l3a, .bc⟩
  | .beki => ⟨.deontic, .l3a, .bc⟩
  | .hazu => ⟨.epistemic, .l2, .bc⟩
  | .yoo => ⟨.evidential, .l2, .bc⟩
  | .rasii => ⟨.evidential, .l2, .bc⟩
  | .kaMoSirenai => ⟨.epistemic, .l2, .bc⟩
  | .soo2 => ⟨.evidential, .l1, .c⟩
  | .daroo => ⟨.epistemic, .l1, .bc⟩
  | .hortative => ⟨.mood, .l0, .cd⟩
  | .imperativeI => ⟨.mood, .l0, .d⟩
  | .imperativeII => ⟨.mood, .l0, .d⟩

/-- A row of Table 49, p. 227: the scope relation of a marker to a category. -/
structure ScopeRow where
  /-- The relation. -/
  scope : Scope
  /-- Whether the table qualifies the relation with a mark. -/
  qualified : Bool
  deriving DecidableEq, Repr

/-- The cells of Table 49, p. 227, by marker and category; counted in a corpus; checked against
the page images. -/
def scopes : Marker → Category → ScopeRow
  | .eru, .stativeAspect => ⟨.both, false⟩
  | .eru, .completiveAspect => ⟨.both, false⟩
  | .eru, .internalNegation => ⟨.both, false⟩
  | .eru, .externalNegation => ⟨.embedded, false⟩
  | .eru, .tense => ⟨.embedded, false⟩
  | .eru, .nominalization => ⟨.both, false⟩
  | .eru, .illocutionaryModulation => ⟨.embedded, false⟩
  | .rareru, .stativeAspect => ⟨.both, false⟩
  | .rareru, .completiveAspect => ⟨.both, false⟩
  | .rareru, .internalNegation => ⟨.both, false⟩
  | .rareru, .externalNegation => ⟨.embedded, false⟩
  | .rareru, .tense => ⟨.embedded, false⟩
  | .rareru, .nominalization => ⟨.both, false⟩
  | .rareru, .illocutionaryModulation => ⟨.embedded, false⟩
  | .kotoGaDekiru, .stativeAspect => ⟨.both, false⟩
  | .kotoGaDekiru, .completiveAspect => ⟨.both, false⟩
  | .kotoGaDekiru, .internalNegation => ⟨.both, false⟩
  | .kotoGaDekiru, .externalNegation => ⟨.embedded, false⟩
  | .kotoGaDekiru, .tense => ⟨.embedded, false⟩
  | .kotoGaDekiru, .nominalization => ⟨.embedded, false⟩
  | .kotoGaDekiru, .illocutionaryModulation => ⟨.embedded, false⟩
  | .soo1, .stativeAspect => ⟨.both, false⟩
  | .soo1, .completiveAspect => ⟨.both, false⟩
  | .soo1, .internalNegation => ⟨.both, false⟩
  | .soo1, .externalNegation => ⟨.both, false⟩
  | .soo1, .tense => ⟨.embedded, false⟩
  | .soo1, .nominalization => ⟨.embedded, false⟩
  | .soo1, .illocutionaryModulation => ⟨.embedded, false⟩
  | .tai, .stativeAspect => ⟨.both, true⟩  -- Embedding by the aspect only in a resultative reading.
  | .tai, .completiveAspect => ⟨.both, false⟩
  | .tai, .internalNegation => ⟨.both, false⟩
  | .tai, .externalNegation => ⟨.embedded, false⟩
  | .tai, .tense => ⟨.both, true⟩  -- Embedding of tense only in the counterfactual past.
  | .tai, .nominalization => ⟨.both, false⟩
  | .tai, .illocutionaryModulation => ⟨.embedded, false⟩
  | .teHosii, .stativeAspect =>  -- Embedding by the aspect only in a resultative reading.
    ⟨.both,
     true⟩
  | .teHosii, .completiveAspect => ⟨.both, false⟩
  | .teHosii, .internalNegation => ⟨.both, false⟩
  | .teHosii, .externalNegation => ⟨.embedded, false⟩
  | .teHosii, .tense => ⟨.both, true⟩  -- Embedding of tense only in the counterfactual past.
  | .teHosii, .nominalization => ⟨.both, false⟩
  | .teHosii, .illocutionaryModulation => ⟨.embedded, false⟩
  | .nakerebaNaranai, .stativeAspect =>  -- Embedding by the aspect only in a resultative reading.
    ⟨.both,
     true⟩
  | .nakerebaNaranai, .completiveAspect => ⟨.both, false⟩
  | .nakerebaNaranai, .internalNegation => ⟨.both, false⟩
  | .nakerebaNaranai, .externalNegation => ⟨.embedded, false⟩
  | .nakerebaNaranai, .tense =>  -- Embedding of tense only in the counterfactual past.
    ⟨.both,
     true⟩
  | .nakerebaNaranai, .nominalization => ⟨.both, false⟩
  | .nakerebaNaranai, .illocutionaryModulation => ⟨.embedded, false⟩
  | .rebaIi, .stativeAspect => ⟨.embeds, false⟩
  | .rebaIi, .completiveAspect => ⟨.embeds, false⟩
  | .rebaIi, .internalNegation => ⟨.both, false⟩
  | .rebaIi, .externalNegation => ⟨.embedded, false⟩
  | .rebaIi, .tense => ⟨.both, true⟩  -- Embedding of tense only in the counterfactual past.
  | .rebaIi, .nominalization => ⟨.both, false⟩
  | .rebaIi, .illocutionaryModulation => ⟨.embedded, false⟩
  | .beki, .stativeAspect => ⟨.embeds, false⟩
  | .beki, .completiveAspect => ⟨.embeds, false⟩
  | .beki, .internalNegation => ⟨.both, false⟩
  | .beki, .externalNegation => ⟨.embedded, false⟩
  | .beki, .tense => ⟨.both, true⟩  -- Embedding of tense only in the counterfactual past.
  | .beki, .nominalization => ⟨.both, false⟩
  | .beki, .illocutionaryModulation => ⟨.embedded, false⟩
  | .hazu, .stativeAspect => ⟨.embeds, false⟩
  | .hazu, .completiveAspect => ⟨.embeds, false⟩
  | .hazu, .internalNegation => ⟨.both, false⟩
  | .hazu, .externalNegation => ⟨.both, false⟩
  | .hazu, .tense => ⟨.both, false⟩
  | .hazu, .nominalization => ⟨.both, false⟩
  | .hazu, .illocutionaryModulation => ⟨.embedded, false⟩
  | .yoo, .stativeAspect => ⟨.embeds, false⟩
  | .yoo, .completiveAspect => ⟨.embeds, false⟩
  | .yoo, .internalNegation => ⟨.both, false⟩
  | .yoo, .externalNegation => ⟨.both, false⟩
  | .yoo, .tense => ⟨.both, false⟩
  | .yoo, .nominalization => ⟨.both, false⟩
  | .yoo, .illocutionaryModulation => ⟨.embedded, false⟩
  | .rasii, .stativeAspect => ⟨.embeds, false⟩
  | .rasii, .completiveAspect => ⟨.embeds, false⟩
  | .rasii, .internalNegation => ⟨.both, false⟩
  | .rasii, .externalNegation => ⟨.both, false⟩
  | .rasii, .tense => ⟨.both, false⟩
  | .rasii, .nominalization => ⟨.both, false⟩
  | .rasii, .illocutionaryModulation => ⟨.embedded, false⟩
  | .kaMoSirenai, .stativeAspect => ⟨.embeds, false⟩
  | .kaMoSirenai, .completiveAspect => ⟨.embeds, false⟩
  | .kaMoSirenai, .internalNegation => ⟨.embeds, false⟩
  | .kaMoSirenai, .externalNegation => ⟨.both, false⟩
  | .kaMoSirenai, .tense => ⟨.both, false⟩
  | .kaMoSirenai, .nominalization => ⟨.both, false⟩
  | .kaMoSirenai, .illocutionaryModulation => ⟨.embedded, false⟩
  | .soo2, .stativeAspect => ⟨.embeds, false⟩
  | .soo2, .completiveAspect => ⟨.embeds, false⟩
  | .soo2, .internalNegation => ⟨.embeds, false⟩
  | .soo2, .externalNegation => ⟨.embeds, false⟩
  | .soo2, .tense => ⟨.both, false⟩
  | .soo2, .nominalization => ⟨.both, false⟩
  | .soo2, .illocutionaryModulation => ⟨.embedded, false⟩
  | .daroo, .stativeAspect => ⟨.embeds, false⟩
  | .daroo, .completiveAspect => ⟨.embeds, false⟩
  | .daroo, .internalNegation => ⟨.embeds, false⟩
  | .daroo, .externalNegation => ⟨.embeds, false⟩
  | .daroo, .tense => ⟨.embeds, false⟩
  | .daroo, .nominalization => ⟨.both, false⟩
  | .daroo, .illocutionaryModulation => ⟨.embedded, false⟩
  | .hortative, .stativeAspect => ⟨.embeds, false⟩
  | .hortative, .completiveAspect => ⟨.embeds, false⟩
  | .hortative, .internalNegation => ⟨.embeds, false⟩
  | .hortative, .externalNegation => ⟨.both, false⟩
  | .hortative, .tense => ⟨.none, false⟩
  | .hortative, .nominalization => ⟨.embeds, false⟩
  | .hortative, .illocutionaryModulation => ⟨.embedded, false⟩
  | .imperativeI, .stativeAspect => ⟨.embeds, false⟩
  | .imperativeI, .completiveAspect => ⟨.embeds, false⟩
  | .imperativeI, .internalNegation => ⟨.embeds, false⟩
  | .imperativeI, .externalNegation => ⟨.none, false⟩
  | .imperativeI, .tense => ⟨.none, false⟩
  | .imperativeI, .nominalization => ⟨.embeds, false⟩
  | .imperativeI, .illocutionaryModulation => ⟨.embedded, true⟩  -- Printed in parentheses.
  | .imperativeII, .stativeAspect => ⟨.embeds, false⟩
  | .imperativeII, .completiveAspect => ⟨.embeds, false⟩
  | .imperativeII, .internalNegation => ⟨.embeds, false⟩
  | .imperativeII, .externalNegation => ⟨.none, false⟩
  | .imperativeII, .tense => ⟨.none, false⟩
  | .imperativeII, .nominalization => ⟨.embeds, false⟩
  | .imperativeII, .illocutionaryModulation => ⟨.embedded, true⟩  -- Printed in parentheses.

end Narrog2009
