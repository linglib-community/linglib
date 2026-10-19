/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.Akan.Phonology
public import Linglib.Fragments.Yoruba.Phonology
public import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Casali (2003): [ATR] value asymmetries and underlying vowel inventory structure

This file formalizes the paper's inventory typology and its account of System-Dependent
[ATR] Dominance. An underlying inventory with a tongue-root contrast is a 5Ht, 4Ht(H) or
4Ht(M) system according to which heights carry the contrast, its footnote 2 (`InventoryType`,
`inventoryType?`, read off a finite set of segments; the schematic inventories (1) are the
witnesses `nineVowel`, `sevenVowelHigh`, `sevenVowelMid`, and the five-vowel system falls
outside). Its survey of 110 Niger-Congo and Nilo-Saharan languages finds [+ATR] dominant
where high vowels contrast and [−ATR] dominant where only mid vowels do, against the System
Independence Hypothesis shared by the Universal [+ATR] Dominance and Variable [ATR] Dominance
theories; the correlation is its hypothesis (20) (`InventoryType.specifiedValue`,
`SystemDependent`), with Kimatuumbi and Legbo the two survey languages it leaves
unexplained. Its two poles are Akan, the nine-vowel 5Ht system whose [+ATR] spreads across word
boundaries and in compounds and lends /a/ a [+ATR] allophone (Table 2), and Standard Yoruba,
the seven-vowel 4Ht(M) system with [−ATR] spreading in compounds (Table 4); both types derive
from the fragments' inventories and both languages conform, while a [+ATR]-dominant Yoruba, its
Yoruba⁺, would not (`akan_conforms`, `yoruba_conforms`, `yoruba_plus_violates`). Section 7
derives the correlation from lexical specification: only the specified value is present
underlyingly, MAX([ATR]) preserves it and *[ATR] penalizes it. Ranked
HARMONY, MAX([ATR])root ≫ *[ATR] ≫ MAX([ATR]), affixes take the root's value whatever the
inputs, its tableaux (21) and (22) (`rootControl_optimal`); promoting MAX([ATR]) above *[ATR]
lets the specified value win from either position, the classic dominant pattern
(`dominant_optimal`); outside a harmonic context the root-control ranking strips an affix of
its specification, so harmonizing affixes surface with the value opposite to the dominant
one, weak assimilatory dominance, where the dominant ranking keeps the affix faithful
(`isolated_optimal`, `isolatedDominant_optimal`); and a ban on [+ATR] low vowels outranking
MAX([ATR]) gives indirect [−ATR] dominance before a low-vowel suffix, its tableau (23)
(`reversal_optimal`).

## Implementation notes

The [ATR] value is `Phonology.Feature.atr` read as `Bool`, `true` for [+ATR]. The paper's
underspecified representations are rendered by constraints that see only the specified
value: a candidate is a fully valued form, and a value is specified when it is the
inventory type's `specifiedValue`. A contrast at a height is a [+ATR] vowel of that height
whose [−ATR] twin is also in the inventory. The survey rows and their counts (Tables 2–7),
section 3's criteria for telling 4Ht(H) from 4Ht(M) systems, and section 6's genetic
discussion are not formalized.

## References

* [casali-2003]
* [hayes-2009]
-/

@[expose] public section

namespace Casali2003

open Phonology OptimalityTheory
open OptimalityTheory (Constraint)

/-! ### Inventory types (1) -/

/-- The three underlying inventory types with an [ATR] contrast, by the heights that carry
it (footnote 2): both high and mid vowels, high vowels only, or mid vowels only. -/
inductive InventoryType where
  | fiveHeight
  | fourHeightHigh
  | fourHeightMid
  deriving DecidableEq, Repr

variable (I : Finset Segment)

/-- An [ATR] contrast among the vowels of `I` satisfying `P` is a [+ATR] member whose [−ATR]
twin is also a member. -/
def HasContrastAmong (P : Segment → Prop) [DecidablePred P] : Prop :=
  ∃ v ∈ I, P v ∧ v.HasValue .atr true ∧ v.setFeature .atr false ∈ I

instance (P : Segment → Prop) [DecidablePred P] : Decidable (HasContrastAmong I P) := by
  unfold HasContrastAmong; infer_instance

/-- The high vowels. -/
def IsHigh (v : Segment) : Prop := v.HasValue .high true

instance : DecidablePred IsHigh := fun v ↦ inferInstanceAs (Decidable (v.HasValue _ _))

/-- The mid vowels. -/
def IsMid (v : Segment) : Prop := v.HasValue .high false ∧ v.HasValue .low false

instance : DecidablePred IsMid := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The inventory type of `I`, when it has a tongue-root contrast at all: five-vowel systems
fall outside the typology. -/
def inventoryType? : Option InventoryType :=
  if HasContrastAmong I IsHigh then
    if HasContrastAmong I IsMid then some .fiveHeight else some .fourHeightHigh
  else if HasContrastAmong I IsMid then some .fourHeightMid else none

/-- A vowel of a schematic inventory is the segment of its chart entry's tongue-root
reading, as in the fragments. -/
def vowel (m : Data.PHOIBLE.FeatureMatrix) : Segment := .ofChart m.tenseAsATR

/-- The nine-vowel 5Ht system /i ɪ e ɛ a ɔ o ʊ u/ of (1a), Akan's. -/
def nineVowel : Finset Segment :=
  {vowel .«i», vowel .«ɪ», vowel .«e», vowel .«ɛ», vowel .«a», vowel .«ɔ», vowel .«o», vowel .«ʊ»,
    vowel .«u»}

/-- The seven-vowel 4Ht(M) system /i e ɛ a ɔ o u/ of (1b), Yoruba's. -/
def sevenVowelMid : Finset Segment :=
  {vowel .«i», vowel .«e», vowel .«ɛ», vowel .«a», vowel .«ɔ», vowel .«o», vowel .«u»}

/-- The seven-vowel 4Ht(H) system /i ɪ ɛ a ɔ ʊ u/ of (1c). -/
def sevenVowelHigh : Finset Segment :=
  {vowel .«i», vowel .«ɪ», vowel .«ɛ», vowel .«a», vowel .«ɔ», vowel .«ʊ», vowel .«u»}

/-- The five-vowel system /i e a o u/, outside the typology. -/
def fiveVowel : Finset Segment := {vowel .«i», vowel .«e», vowel .«a», vowel .«o», vowel .«u»}

/-- The 5Ht system (1a) is Akan's vowel inventory. -/
theorem nineVowel_eq : nineVowel = Akan.vowels := by decide

/-- The 4Ht(M) system (1b) is Yoruba's vowel inventory. -/
theorem sevenVowelMid_eq : sevenVowelMid = Yoruba.vowels := by decide

/-- The schematic inventories of (1) receive their types, and the five-vowel system none. -/
theorem inventoryType?_schematic :
    inventoryType? nineVowel = some .fiveHeight ∧
      inventoryType? sevenVowelHigh = some .fourHeightHigh ∧
      inventoryType? sevenVowelMid = some .fourHeightMid ∧
      inventoryType? fiveVowel = none := by
  decide

/-! ### System-Dependent [ATR] Dominance (20) -/

/-- The lexically specified, hence systematically dominant, [ATR] value is [+ATR] where high
vowels contrast and [−ATR] where only mid vowels do. -/
def InventoryType.specifiedValue : InventoryType → Bool
  | .fiveHeight | .fourHeightHigh => true
  | .fourHeightMid => false

/-- System-Dependent [ATR] Dominance (20): a language the typology classifies has its
inventory type's specified value as its systematically dominant value. -/
def SystemDependent (dominant : Bool) : Prop :=
  ∀ T ∈ inventoryType? I, dominant = T.specifiedValue

instance (dominant : Bool) : Decidable (SystemDependent I dominant) := by
  unfold SystemDependent; infer_instance

/-! ### Two survey languages -/

/-- Akan's nine vowels form a 5Ht system, and its [+ATR] dominance (Table 2) conforms to
(20); the [−ATR] spreading from a dominant affix it also shows (Table 5) is the indirect
kind. -/
theorem akan_conforms :
    inventoryType? Akan.vowels = some .fiveHeight ∧
      SystemDependent Akan.vowels true := by
  decide

/-- Standard Yoruba's seven vowels form a 4Ht(M) system, and its [−ATR] dominance
(Table 4) conforms to (20). -/
theorem yoruba_conforms :
    inventoryType? Yoruba.vowels = some .fourHeightMid ∧
      SystemDependent Yoruba.vowels false := by
  decide

/-- Yoruba⁺, a 4Ht(M) language with [+ATR] dominance, would violate (20), the typological
gap the survey finds nearly empty. -/
theorem yoruba_plus_violates : ¬ SystemDependent Yoruba.vowels true := by decide

/-! ### Section 7: dominance from inventory-dependent specification

Only the specified value `s` is present underlyingly. MAX([ATR]) and its root-specific
version demand that specified input values survive; *[ATR] penalizes each specified value
on the surface; HARMONY demands agreement. -/

/-- The [ATR] values of a root and an affix. -/
structure Word where
  root  : Bool
  affix : Bool
  deriving DecidableEq, Repr

variable (s : Bool) (w : Word)

/-- HARMONY requires root and affix to agree. -/
def harmony : Constraint Word := .binary fun o ↦ o.root ≠ o.affix

/-- MAX([ATR])root requires a specified root value to survive. -/
def maxRoot : Constraint Word := .binary fun o ↦ w.root = s ∧ o.root ≠ s

/-- MAX([ATR]) requires every specified input value to survive, with one violation per loss. -/
def maxAtr : Constraint Word := fun o ↦
  (if w.root = s ∧ o.root ≠ s then 1 else 0) + if w.affix = s ∧ o.affix ≠ s then 1 else 0

/-- *[ATR] assigns one violation per specified value on the surface. -/
def starAtr : Constraint Word := fun o ↦
  (if o.root = s then 1 else 0) + if o.affix = s then 1 else 0

/-- The four outputs for a root–affix input. -/
def outputs : Finset Word :=
  {⟨true, true⟩, ⟨true, false⟩, ⟨false, true⟩, ⟨false, false⟩}

/-- The root-control ranking HARMONY, MAX([ATR])root ≫ *[ATR] ≫ MAX([ATR]) over the outputs
for input `w`: the tableaux (21) and (22). -/
def rootControl : Tableau Word 4 :=
  Tableau.ofList outputs [harmony, maxRoot s w, starAtr s, maxAtr s w]

/-- Under root control the affix takes the root's value, whatever the inputs and whichever
value is specified: (21) and (22). -/
theorem rootControl_optimal : (rootControl s w).optimal = {⟨w.root, w.root⟩} := by
  obtain ⟨r, a⟩ := w
  cases s <;> cases r <;> cases a <;> decide

/-- The dominant ranking promotes MAX([ATR]) above *[ATR]. -/
def dominant : Tableau Word 4 :=
  Tableau.ofList outputs [harmony, maxRoot s w, maxAtr s w, starAtr s]

/-- A dominant system assigns the specified value when either input carries it. -/
def Word.dominantValue : Bool := if w.root = s ∨ w.affix = s then s else !s

/-- Under the dominant ranking the specified value spreads from root or affix alike, the
classic dominant–recessive pattern. -/
theorem dominant_optimal :
    (dominant s w).optimal = {⟨w.dominantValue s, w.dominantValue s⟩} := by
  obtain ⟨r, a⟩ := w
  cases s <;> cases r <;> cases a <;> decide

variable (a : Bool)

/-- An affix outside any harmonic context under the root-control order *[ATR] ≫ MAX([ATR]),
over its two surface values. -/
def isolated : Tableau Bool 2 :=
  Tableau.ofList {true, false} [.binary (· = s), .binary fun o ↦ a = s ∧ o ≠ s]

/-- The same affix under the dominant order MAX([ATR]) ≫ *[ATR]. -/
def isolatedDominant : Tableau Bool 2 :=
  Tableau.ofList {true, false} [.binary fun o ↦ a = s ∧ o ≠ s, .binary (· = s)]

/-- Outside harmony a root-control system strips an affix of its specification, so
harmonizing affixes surface with the value opposite to the dominant one: weak assimilatory
dominance of `s`. -/
theorem isolated_optimal : (isolated s a).optimal = {!s} := by
  cases s <;> cases a <;> decide

/-- Under the dominant order an isolated affix keeps its value. -/
theorem isolatedDominant_optimal : (isolatedDominant s a).optimal = {a} := by
  cases s <;> cases a <;> decide

/-! ### Dominance reversal (23) -/

/-- An output for the input /tol-a/ of (23), a [+ATR] root with a [−ATR] low suffix in a
5Ht language, records the root's value and the suffix's [ATR] and [low] values. -/
structure LowSuffixCand where
  root      : Bool
  suffixAtr : Bool
  suffixLow : Bool
  deriving DecidableEq, Repr

/-- Tableau (23) ranks *[+ATR, +low] and the preservation of [+low] above HARMONY above
MAX([ATR]), over [tola], [tɔla], [tolæ] and [tole]. -/
def reversal : Tableau LowSuffixCand 4 :=
  Tableau.ofList
    {⟨true, false, true⟩, ⟨false, false, true⟩, ⟨true, true, true⟩,
      ⟨true, true, false⟩}
    [.binary fun c ↦ c.suffixAtr ∧ c.suffixLow, .binary fun c ↦ ¬ c.suffixLow,
      .binary fun c ↦ c.root ≠ c.suffixAtr, .binary fun c ↦ ¬ c.root]

/-- The root loses its [+ATR] to the low suffix, [tɔla], which is indirect [−ATR] dominance in
a language whose specified value is [+ATR]. -/
theorem reversal_optimal : reversal.optimal = {⟨false, false, true⟩} := by decide

end Casali2003
