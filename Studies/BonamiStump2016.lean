module

public import Linglib.Morphology.Paradigm.Function
public import Linglib.Morphology.Word.Features
public import Mathlib.Tactic.DeriveFintype

/-!
# Bonami and Stump 2016: Paradigm Function Morphology

This file formalizes the worked PFM1 fragments of Bonami and Stump's chapter on the engine of
`Morphology/Paradigm/Function.lean`, with property sets as feature bundles: the paradigm function of
the Icelandic verbs, the Sanskrit ninth-conjugation portmanteau, and the Sanskrit vocative rule of
referral. The Icelandic rules meet Pāṇinian Determinism at every cell of (3), but under the
chapter's narrowness (15) the weak-class theme vowel `-a` preempts the present subjunctive `-i`, so
they derive *kalla* and *ætla* where Table 17.1 has *kalli* and *ætli*.

## Main definitions

* `cells`: the twenty-seven well-formed and complete property sets (3) of an Icelandic verb.
* `strong1a`, `stemChoice`: the metarule (8) and basic stem choice by the rules (7) and (9).
* `IsPaniniWellFormed`: Stump's Pāṇinian well-formedness condition on a rule set.
* `blockI`, `blockII`, `blockIII`, `pf`: the blocks of Table 17.3 and the paradigm function (13).
* `pfNinth`: the Sanskrit paradigm function (21), over the portmanteau block `[ii,i]` of (20).
* `caseBlock`: a Sanskrit case block with the vocative rule of referral (17).

## Main results

* `pf_kalla`, `pf_gripa_imp`, `pf_fljuga`, `pf_gripa_pst`: (4a), (4c), (4d), and *greipst*.
* `stem_gripa`, `stem_bita`, `strong1a_card`: (7c), (7d) and (10) are theorems of (8), and
  (7c), (7d) and (7e) apply to three, twelve and twenty-seven cells.
* `isPaniniWellFormed`: the rules (7) and each block of Table 17.3 have a narrowest applicable
  rule at every cell of (3), no two of their rules alike.
* `nar_aetla_imp`, `blockIII_narrowness`: the examples of (14) and (15).
* `themeA_lt_sbjvI`, `pf_kalla_sbjv`, `pf_aetla_sbjv`: by clause (ii) of (15), `-a` preempts
  `-i`, against Table 17.1 and the inputs *ætli-um*, *ætli-ið* of Table 17.4.
* `as_portmanteau`, `kri_fcd`, `kri_composition`: (22) and (23) by the FCD (24), Table 17.5.
* `voc_refers_to_nom`, `voc_du`: the vocative dual of DĀNA patterns after the nominative.

## Implementation notes

The metageneralizations (18) are phonological, so the decided cells are ones they leave untouched,
and FLJÚGA's ablaut alternants are basic stems, as in the chapter. Table 17.3 has no rule for the
strong verbs' past plural `-u`, past subjunctive `-i` or epenthetic `u` (*gripu*, *gripi*,
*grípur*). The consonant-final roots of (20c) form the class `{AŚ}`.

## References

* [bonami-stump-2016]
* [stump-2001]
-/

@[expose] public section

namespace BonamiStump2016

open Morphology Morphology.Exponence Morphology.PFM

/-! ### Icelandic verbs -/

section Icelandic

/-- The verbs of Table 17.1, KALLA (weak.4.a), ÆTLA (weak.4.b), GRÍPA (strong.1.a) and FLJÚGA
(strong.2.b), and BÍTA (strong.1.a) of (9). -/
inductive Verb | kalla | aetla | gripa | fljuga | bita
  deriving DecidableEq, Fintype

open Verb

/-- The finite property set of mood `m`, tense `t`, person `p` and number `n`. -/
def finite (m : UD.Mood) (t : UD.Tense) (p : Person) (n : Number) : Features :=
  .of (person := some p) (number := some n) (tense := some t) (mood := some m)

/-- The imperative property set of person `p` and number `n`. -/
def imperative (p : Person) (n : Number) : Features :=
  .of (person := some p) (number := some n) (mood := some .Imp)

/-- The well-formed and complete property sets (3): the indicative and subjunctive in each tense,
person and number, and the second singular and first and second plural imperatives. -/
def cells : Finset Features :=
  ((({.Ind, .Sub} : Finset UD.Mood) ×ˢ ({.Pres, .Past} : Finset UD.Tense)) ×ˢ
      (({.first, .second, .third} : Finset Person) ×ˢ ({.singular, .plural} : Finset Number))).image
    (fun ⟨⟨m, t⟩, p, n⟩ ↦ finite m t p n) ∪
  ({(.second, .singular), (.first, .plural), (.second, .plural)} : Finset (Person × Number)).image
    fun ⟨p, n⟩ ↦ imperative p n

example : cells.card = 27 := by decide

local notation "ExpoRule" => PFM.Rule Verb Features (Action Verb String Features)

/-- The weak verbs, all of conjugation 4. -/
def weak : Finset Verb := {kalla, aetla}
/-- Weak conjugation 4.b. -/
def weak4b : Finset Verb := {aetla}
/-- The strong verbs. -/
def strong : Finset Verb := {gripa, fljuga, bita}

/-- The weak past plural theme vowel `-u`. -/
def themeU : ExpoRule :=
  ⟨weak, .of (number := some .plural) (tense := some .Past), .const (· ++ "u")⟩
/-- The present subjunctive `-i`. -/
def sbjvI : ExpoRule :=
  ⟨Finset.univ, .of (tense := some .Pres) (mood := some .Sub), .const (· ++ "i")⟩
/-- The weak theme vowel `-a`. -/
def themeA : ExpoRule := ⟨weak, ⊥, .const (· ++ "a")⟩

/-- Block I of Table 17.3 realizes the theme vowels. -/
def blockI : Block Verb String Features := [themeU, sbjvI, themeA, identityDefault]

/-- Block II of Table 17.3 realizes past tense. -/
def blockII : Block Verb String Features :=
  [ ⟨weak, .of (number := some .singular) (tense := some .Past), .const (· ++ "ði")⟩,
    ⟨weak, .of (number := some .plural) (tense := some .Past), .const (· ++ "ðu")⟩,
    identityDefault ]

/-- The weak.4.b imperative `-ðu`. -/
def weak4bImp : ExpoRule := ⟨weak4b, imperative .second .singular, .const (· ++ "ðu")⟩
/-- The zero exponent of the second-singular imperative. -/
def zeroImp : ExpoRule := ⟨Finset.univ, imperative .second .singular, .const id⟩
/-- The general second-singular `-r`. -/
def rSg2 : ExpoRule :=
  ⟨Finset.univ, .of (person := some .second) (number := some .singular), .const (· ++ "r")⟩

/-- Block III of Table 17.3 realizes agreement and mood. -/
def blockIII : Block Verb String Features :=
  [ weak4bImp, zeroImp, rSg2,
    ⟨Finset.univ, finite .Ind .Pres .third .singular, .const (· ++ "r")⟩,
    ⟨Finset.univ, .of (person := some .first) (number := some .plural), .const (· ++ "um")⟩,
    ⟨Finset.univ, .of (person := some .second) (number := some .plural), .const (· ++ "ið")⟩,
    ⟨Finset.univ, finite .Ind .Pres .third .plural, .const (· ++ "a")⟩,
    ⟨strong, finite .Ind .Past .second .singular, .const (· ++ "st")⟩,
    identityDefault ]

/-- The metarule (8): a strong.1.a verb with default stem `XíY` has the singular indicative past
stem `XeiY` and the past stem `XiY`. -/
def strong1a (v : Verb) (x y : String) : RuleSet (PFM.Rule Verb Features String) :=
  [ ⟨{v}, .of (number := some .singular) (tense := some .Past) (mood := some .Ind), x ++ "ei" ++ y⟩,
    ⟨{v}, .of (tense := some .Past), x ++ "i" ++ y⟩,
    ⟨{v}, ⊥, x ++ "í" ++ y⟩ ]

/-- The rules of basic stem choice (7), with (7c)–(7e) and the default stem (9) of BÍTA expanded by
the metarule (8), and FLJÚGA's ablaut alternants listed as stems. -/
def iceStems : RuleSet (PFM.Rule Verb Features String) :=
  [⟨{kalla}, ⊥, "kall"⟩, ⟨{aetla}, ⊥, "ætl"⟩] ++ strong1a gripa "gr" "p" ++ strong1a bita "b" "t" ++
  [ ⟨{fljuga}, .of (number := some .singular) (tense := some .Past) (mood := some .Ind), "flaug"⟩,
    ⟨{fljuga}, .of (tense := some .Past) (mood := some .Ind), "flug"⟩,
    ⟨{fljuga}, .of (tense := some .Past), "flyg"⟩,
    ⟨{fljuga}, .of (number := some .singular) (tense := some .Pres) (mood := some .Ind), "flýg"⟩,
    ⟨{fljuga}, ⊥, "fljúg"⟩ ]

/-- Basic stem choice gives a cell the stem of its narrowest applicable rule of (7). -/
def stemChoice : Verb × Features → String :=
  iceStems.realizeMinimalD Rule.narrowness fun _ ↦ ""

/-- The Icelandic paradigm function (13) applies basic stem choice and then Blocks I–III. -/
def pf (v : Verb) (σ : Features) : String :=
  paradigmFunction stemChoice [blockI, blockII, blockIII] (v, σ)

/-- KALLA's second-singular indicative past is `kall` + `-a` + `-ði` + `-r`. -/
theorem pf_kalla : pf kalla (finite .Ind .Past .second .singular) = "kallaðir" := by decide

/-- GRÍPA's second-singular imperative is the bare stem, the zero exponent preempting `-r`. -/
theorem pf_gripa_imp : pf gripa (imperative .second .singular) = "gríp" := by decide

/-- FLJÚGA's first-singular indicative past is the stem of its narrowest rule of (7). -/
theorem pf_fljuga : pf fljuga (finite .Ind .Past .first .singular) = "flaug" := by decide

/-- GRÍPA's second-singular indicative past takes the strong `-st`, which preempts `-r`. -/
theorem pf_gripa_pst : pf gripa (finite .Ind .Past .second .singular) = "greipst" := by decide

/-- GRÍPA's singular indicative past stem is `greip` and its past stem `grip`, by (8). -/
theorem stem_gripa : stemChoice (gripa, finite .Ind .Past .first .singular) = "greip" ∧
    stemChoice (gripa, finite .Sub .Past .first .singular) = "grip" := by decide

/-- BÍTA's singular indicative past stem is `beit` and its past stem `bit`, by (8). -/
theorem stem_bita : stemChoice (bita, finite .Ind .Past .first .singular) = "beit" ∧
    stemChoice (bita, finite .Sub .Past .first .singular) = "bit" := by decide

/-- The rules (7c), (7d) and (7e) apply to three, twelve and twenty-seven cells. -/
theorem strong1a_card :
    (strong1a gripa "gr" "p").map (fun r ↦ (cells.filter (r.props ≤ ·)).card) = [3, 12, 27] := by
  decide

/-- Stump's Pāṇinian well-formedness condition on a rule set: no two rules are equally narrow, and
some applicable rule is narrowest at every cell of (3). -/
def IsPaniniWellFormed {F : Type} (v : RuleSet (PFM.Rule Verb Features F)) : Prop :=
  (v.map Rule.narrowness).Nodup ∧ ∀ l, ∀ σ ∈ cells, v.HasMostSpecific Rule.narrowness (l, σ)

instance {F : Type} (v : RuleSet (PFM.Rule Verb Features F)) : Decidable (IsPaniniWellFormed v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The rules (7) and Blocks I–III meet the Pāṇinian well-formedness condition. -/
theorem isPaniniWellFormed : IsPaniniWellFormed iceStems ∧ IsPaniniWellFormed blockI ∧
    IsPaniniWellFormed blockII ∧ IsPaniniWellFormed blockIII := by
  decide

/-- The present subjunctive `-i` and the first-plural `-um` cannot share a block, since both apply
in the first-plural present subjunctive and neither is narrower. -/
example : ¬ IsPaniniWellFormed [sbjvI,
    ⟨Finset.univ, .of (person := some .first) (number := some .plural), .const (· ++ "um")⟩] := by
  decide

/-- Block III realizes ÆTLA's second-singular imperative with `-ðu`. -/
theorem nar_aetla_imp : blockIII.eval (aetla, imperative .second .singular) "ætla" = "ætlaðu" := by
  decide

/-- The weak.4.b `-ðu` is narrower than the zero imperative, which is narrower than `-r`. -/
theorem blockIII_narrowness :
    weak4bImp.narrowness < zeroImp.narrowness ∧ zeroImp.narrowness < rSg2.narrowness := by
  decide

/-- The weak-class `-a` is narrower than the verb-class `-i`, whatever their property sets. -/
theorem themeA_lt_sbjvI : themeA.narrowness < sbjvI.narrowness := by decide

/-- KALLA's first-singular present subjunctive comes out `kalla`, not Table 17.1's `kalli`. -/
theorem pf_kalla_sbjv : pf kalla (finite .Sub .Pres .first .singular) = "kalla" := by decide

/-- ÆTLA's first-plural present subjunctive comes out `ætla-um`, not Table 17.4's `ætli-um`. -/
theorem pf_aetla_sbjv : pf aetla (finite .Sub .Pres .first .plural) = "ætlaum" := by decide

/-- The Identity Function Default fills Block I for a strong verb in the indicative. -/
example : blockI.eval (gripa, finite .Ind .Pres .first .singular) "gríp" = "gríp" := by decide

end Icelandic

/-! ### Sanskrit portmanteau and the Function Composition Default -/

section Portmanteau

/-- The ninth-conjugation verbs AŚ 'eat', whose root ends in a consonant, and KRĪ 'buy'. -/
inductive NinthVerb | as | kri
  deriving DecidableEq, Fintype

open NinthVerb

/-- The second-person singular imperative active. -/
def imp2sgAct : Features :=
  .of (person := some .second) (number := some .singular) (mood := some .Imp) (voice := some .Act)

/-- Block i (20a) realizes the ninth-conjugation `-nī`. -/
def blockNi : Block NinthVerb String Features :=
  [⟨Finset.univ, ⊥, .const (· ++ "nī")⟩]

/-- Block ii (20b) realizes the second-singular imperative active `-hi`. -/
def blockHi : Block NinthVerb String Features :=
  [⟨Finset.univ, imp2sgAct, .const (· ++ "hi")⟩]

/-- The rule (20c) of Block [ii,i] realizes `-āna` after a consonant-final root. -/
def blockAna : Block NinthVerb String Features :=
  [⟨{as}, imp2sgAct, .const (· ++ "āna")⟩]

/-- The roots of AŚ and KRĪ. -/
def root : NinthVerb → String
  | as => "aś"
  | kri => "krī"

/-- The Sanskrit paradigm function (21) applies Block [ii,i] to the root. -/
def pfNinth (v : NinthVerb) (σ : Features) : String :=
  paradigmFunction (fun c ↦ root c.1) [blockAna.portmanteau blockHi blockNi] (v, σ)

/-- AŚ takes the portmanteau `-āna`. -/
theorem as_portmanteau : pfNinth as imp2sgAct = "aśāna" := by decide

/-- No portmanteau rule applies to KRĪ, so Block [ii,i] is the composition of Blocks ii and i. -/
theorem kri_fcd : pfNinth kri imp2sgAct =
    blockHi.eval (kri, imp2sgAct) (blockNi.eval (kri, imp2sgAct) "krī") := by
  simp only [pfNinth, paradigmFunction, evalBlocks_cons, evalBlocks_nil, root]
  exact Block.eval_portmanteau_of_applicable_eq_nil (by decide) _

/-- The composition gives KRĪ's `krīnīhi`. -/
theorem kri_composition : pfNinth kri imp2sgAct = "krīnīhi" := by decide

end Portmanteau

/-! ### Sanskrit vocative referral -/

section Referral

/-- The neuter a-stem DĀNA 'gift' of Table 17.2. -/
inductive Noun | dana
  deriving DecidableEq, Fintype

open Noun

/-- The property set of case `k` and number `n`. -/
def nominal (k : Case) (n : Number) : Features := .of (number := some n) (case_ := some k)

/-- The property set `σ/{nom}` of (17) is `σ` with nominative case. -/
def toNom (σ : Features) : Features := Function.update σ .case (some Case.nom)

/-- Block i holds the nominative dual exponent and the vocative rule of referral (17). -/
def caseBlock : Block Noun String Features :=
  [ ⟨Finset.univ, nominal .nom .dual, .const (· ++ "e")⟩,
    ⟨Finset.univ, .of (case_ := some .voc), .referral toNom⟩ ]

/-- The vocative dual takes the nominative dual's exponent. -/
theorem voc_refers_to_nom : caseBlock.eval (dana, nominal .voc .dual) "dān" =
    caseBlock.eval (dana, nominal .nom .dual) "dān" := by decide

/-- The vocative dual of DĀNA is `dāne`. -/
theorem voc_du : caseBlock.eval (dana, nominal .voc .dual) "dān" = "dāne" := by decide

end Referral

end BonamiStump2016
