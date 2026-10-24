module

public import Linglib.Morphology.Paradigm.Function
public import Mathlib.Tactic.DeriveFintype

/-!
# Bonami and Stump 2016: Paradigm Function Morphology

This file formalizes the worked PFM1 fragments of Bonami and Stump's chapter on the engine of
`Morphology/Paradigm/Function.lean`: the paradigm function of four Icelandic verbs, the Sanskrit
ninth-conjugation portmanteau, and the Sanskrit vocative rule of referral. Under the chapter's
narrowness (15) the weak-class theme vowel `-a` preempts the present subjunctive `-i`, so the
Icelandic rules derive *kalla* and *ætla* where Table 17.1 has *kalli* and *ætli*.

## Main definitions

* `stemChoice`, `blockI`, `blockII`, `blockIII`, `pf`: basic stem choice by the rules (7), the
  blocks of Table 17.3, and the Icelandic paradigm function (13).
* `pfNinth`: the Sanskrit paradigm function (21), over the portmanteau block `[ii,i]` of (20).
* `caseBlock`: a Sanskrit case block with the vocative rule of referral (17).

## Main results

* `pf_kalla`, `pf_gripa_imp`, `pf_fljuga`, `pf_gripa_pst`: (4a), (4c), (4d), and *greipst*.
* `stem_gripa_pst`, `nar_aetla_imp`, `blockIII_narrowness`: the conflict of (7c)–(7e), (14), (15).
* `themeA_lt_sbjvI`, `pf_kalla_sbjv`, `pf_aetla_sbjv`: by clause (ii) of (15), `-a` preempts
  `-i`, against Table 17.1 and the inputs *ætli-um*, *ætli-ið* of Table 17.4.
* `as_portmanteau`, `kri_fcd`, `kri_composition`: (22) and (23) by the FCD (24), Table 17.5.
* `voc_refers_to_nom`, `voc_du`: the vocative dual of DĀNA patterns after the nominative.

## Implementation notes

The metageneralizations (18) are phonological, so the decided cells are ones they leave untouched,
and the strong verbs' ablaut alternants are basic stems, as in the chapter. Table 17.3 has no rule
for the strong verbs' past plural `-u`, past subjunctive `-i` or epenthetic `u` (*gripu*, *gripi*,
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

/-- The verbs of Table 17.1: KALLA (weak.4.a), ÆTLA (weak.4.b), GRÍPA (strong.1.a) and FLJÚGA
(strong.2.b). -/
inductive Verb | kalla | aetla | gripa | fljuga
  deriving DecidableEq, Fintype

/-- Morphosyntactic properties, with person and number separate as in the chapter's `{pst sg}`. -/
inductive Feat | ind | sbjv | imp | prs | pst | p1 | p2 | p3 | sg | pl
  deriving DecidableEq, Fintype

open Verb Feat

local notation "ExpoRule" => PFM.Rule Verb (Finset Feat) (Action Verb String (Finset Feat))

/-- The weak verbs, all of conjugation 4. -/
def weak : Finset Verb := {kalla, aetla}
/-- Weak conjugation 4.b. -/
def weak4b : Finset Verb := {aetla}
/-- The strong verbs. -/
def strong : Finset Verb := {gripa, fljuga}

/-- The weak past plural theme vowel `-u`. -/
def themeU : ExpoRule := ⟨weak, {pst, pl}, .const (· ++ "u")⟩
/-- The present subjunctive `-i`. -/
def sbjvI : ExpoRule := ⟨Finset.univ, {sbjv, prs}, .const (· ++ "i")⟩
/-- The weak theme vowel `-a`. -/
def themeA : ExpoRule := ⟨weak, {}, .const (· ++ "a")⟩

/-- Block I of Table 17.3 realizes the theme vowels. -/
def blockI : Block Verb String (Finset Feat) := [themeU, sbjvI, themeA, identityDefault]

/-- Block II of Table 17.3 realizes past tense. -/
def blockII : Block Verb String (Finset Feat) :=
  [ ⟨weak, {pst, sg}, .const (· ++ "ði")⟩,
    ⟨weak, {pst, pl}, .const (· ++ "ðu")⟩,
    identityDefault ]

/-- The weak.4.b imperative `-ðu`. -/
def weak4bImp : ExpoRule := ⟨weak4b, {imp, p2, sg}, .const (· ++ "ðu")⟩
/-- The zero exponent of the second-singular imperative. -/
def zeroImp : ExpoRule := ⟨Finset.univ, {imp, p2, sg}, .const id⟩
/-- The general second-singular `-r`. -/
def rSg2 : ExpoRule := ⟨Finset.univ, {p2, sg}, .const (· ++ "r")⟩

/-- Block III of Table 17.3 realizes agreement and mood. -/
def blockIII : Block Verb String (Finset Feat) :=
  [ weak4bImp, zeroImp, rSg2,
    ⟨Finset.univ, {ind, prs, p3, sg}, .const (· ++ "r")⟩,
    ⟨Finset.univ, {p1, pl}, .const (· ++ "um")⟩,
    ⟨Finset.univ, {p2, pl}, .const (· ++ "ið")⟩,
    ⟨Finset.univ, {ind, prs, p3, pl}, .const (· ++ "a")⟩,
    ⟨strong, {ind, pst, p2, sg}, .const (· ++ "st")⟩,
    identityDefault ]

/-- The rules of basic stem choice (7), the strong verbs' ablaut alternants listed as stems. -/
def iceStems : RuleSet (PFM.Rule Verb (Finset Feat) String) :=
  [ ⟨{kalla}, {}, "kall"⟩,
    ⟨{aetla}, {}, "ætl"⟩,
    ⟨{gripa}, {ind, pst, sg}, "greip"⟩,
    ⟨{gripa}, {pst}, "grip"⟩,
    ⟨{gripa}, {}, "gríp"⟩,
    ⟨{fljuga}, {ind, pst, sg}, "flaug"⟩,
    ⟨{fljuga}, {ind, pst}, "flug"⟩,
    ⟨{fljuga}, {pst}, "flyg"⟩,
    ⟨{fljuga}, {ind, prs, sg}, "flýg"⟩,
    ⟨{fljuga}, {}, "fljúg"⟩ ]

/-- Basic stem choice gives a cell the stem of its narrowest applicable rule of (7). -/
def stemChoice : Verb × Finset Feat → String :=
  iceStems.realizeMinimalD Rule.narrowness fun _ ↦ ""

/-- The Icelandic paradigm function (13) applies basic stem choice and then Blocks I–III. -/
def pf (v : Verb) (σ : Finset Feat) : String :=
  paradigmFunction stemChoice [blockI, blockII, blockIII] (v, σ)

/-- KALLA's second-singular indicative past is `kall` + `-a` + `-ði` + `-r`. -/
theorem pf_kalla : pf kalla {ind, pst, p2, sg} = "kallaðir" := by decide

/-- GRÍPA's second-singular imperative is the bare stem, the zero exponent preempting `-r`. -/
theorem pf_gripa_imp : pf gripa {imp, p2, sg} = "gríp" := by decide

/-- FLJÚGA's first-singular indicative past is the stem of its narrowest rule of (7). -/
theorem pf_fljuga : pf fljuga {ind, pst, p1, sg} = "flaug" := by decide

/-- GRÍPA's second-singular indicative past takes the strong `-st`, which preempts `-r`. -/
theorem pf_gripa_pst : pf gripa {ind, pst, p2, sg} = "greipst" := by decide

/-- The three-cell rule (7c) is the narrowest stem rule for GRÍPA's first-singular past. -/
theorem stem_gripa_pst : stemChoice (gripa, {ind, pst, p1, sg}) = "greip" := by decide

/-- Block III realizes ÆTLA's second-singular imperative with `-ðu`. -/
theorem nar_aetla_imp : blockIII.eval (aetla, {imp, p2, sg}) "ætla" = "ætlaðu" := by decide

/-- The weak.4.b `-ðu` is narrower than the zero imperative, which is narrower than `-r`. -/
theorem blockIII_narrowness :
    weak4bImp.narrowness < zeroImp.narrowness ∧ zeroImp.narrowness < rSg2.narrowness := by
  decide

/-- The weak-class `-a` is narrower than the verb-class `-i`, whatever their property sets. -/
theorem themeA_lt_sbjvI : themeA.narrowness < sbjvI.narrowness := by decide

/-- KALLA's first-singular present subjunctive comes out `kalla`, not Table 17.1's `kalli`. -/
theorem pf_kalla_sbjv : pf kalla {sbjv, prs, p1, sg} = "kalla" := by decide

/-- ÆTLA's first-plural present subjunctive comes out `ætla-um`, not Table 17.4's `ætli-um`. -/
theorem pf_aetla_sbjv : pf aetla {sbjv, prs, p1, pl} = "ætlaum" := by decide

/-- The Identity Function Default fills Block I for a strong verb in the indicative. -/
example : blockI.eval (gripa, {ind, prs, p1, sg}) "gríp" = "gríp" := by decide

end Icelandic

/-! ### Sanskrit portmanteau and the Function Composition Default -/

section Portmanteau

/-- The ninth-conjugation verbs AŚ 'eat', whose root ends in a consonant, and KRĪ 'buy'. -/
inductive NinthVerb | as | kri
  deriving DecidableEq, Fintype

/-- The properties of the second-person singular imperative active. -/
inductive SF | p2 | sg | imp | act
  deriving DecidableEq, Fintype

open NinthVerb SF

/-- Block i (20a) realizes the ninth-conjugation `-nī`. -/
def blockNi : Block NinthVerb String (Finset SF) :=
  [⟨Finset.univ, {}, .const (· ++ "nī")⟩]

/-- Block ii (20b) realizes the second-singular imperative active `-hi`. -/
def blockHi : Block NinthVerb String (Finset SF) :=
  [⟨Finset.univ, {p2, sg, imp, act}, .const (· ++ "hi")⟩]

/-- The rule (20c) of Block [ii,i] realizes `-āna` after a consonant-final root. -/
def blockAna : Block NinthVerb String (Finset SF) :=
  [⟨{as}, {p2, sg, imp, act}, .const (· ++ "āna")⟩]

/-- The roots of AŚ and KRĪ. -/
def root : NinthVerb → String
  | as => "aś"
  | kri => "krī"

/-- The Sanskrit paradigm function (21) applies Block [ii,i] to the root. -/
def pfNinth (v : NinthVerb) (σ : Finset SF) : String :=
  paradigmFunction (fun c ↦ root c.1) [blockAna.portmanteau blockHi blockNi] (v, σ)

/-- AŚ takes the portmanteau `-āna`. -/
theorem as_portmanteau : pfNinth as {p2, sg, imp, act} = "aśāna" := by decide

/-- No portmanteau rule applies to KRĪ, so Block [ii,i] is the composition of Blocks ii and i. -/
theorem kri_fcd : pfNinth kri {p2, sg, imp, act} =
    blockHi.eval (kri, {p2, sg, imp, act}) (blockNi.eval (kri, {p2, sg, imp, act}) "krī") := by
  simp only [pfNinth, paradigmFunction, evalBlocks_cons, evalBlocks_nil, root]
  exact Block.eval_portmanteau_of_applicable_eq_nil rfl _

/-- The composition gives KRĪ's `krīnīhi`. -/
theorem kri_composition : pfNinth kri {p2, sg, imp, act} = "krīnīhi" := by decide

end Portmanteau

/-! ### Sanskrit vocative referral -/

section Referral

/-- The neuter a-stem DĀNA 'gift' of Table 17.2. -/
inductive Noun | dana
  deriving DecidableEq, Fintype

/-- Case and number properties. -/
inductive NF | nom | voc | du
  deriving DecidableEq, Fintype

open Noun NF

/-- The property set `σ/{nom}` of (17) is `σ` with nominative case. -/
def toNom (σ : Finset NF) : Finset NF := insert nom (σ.erase voc)

/-- Block i holds the nominative dual exponent and the vocative rule of referral (17). -/
def caseBlock : Block Noun String (Finset NF) :=
  [ ⟨Finset.univ, {nom, du}, .const (· ++ "e")⟩,
    ⟨Finset.univ, {voc}, .referral toNom⟩ ]

/-- The vocative dual takes the nominative dual's exponent. -/
theorem voc_refers_to_nom :
    caseBlock.eval (dana, {voc, du}) "dān" = caseBlock.eval (dana, {nom, du}) "dān" := by decide

/-- The vocative dual of DĀNA is `dāne`. -/
theorem voc_du : caseBlock.eval (dana, {voc, du}) "dān" = "dāne" := by decide

end Referral

end BonamiStump2016
