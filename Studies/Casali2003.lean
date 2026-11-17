/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.Akan.Phonology
public import Linglib.Fragments.Yoruba.Phonology
public import Linglib.Phonology.OptimalityTheory.Typology
public import Mathlib.Tactic.DeriveFintype

/-!
# Casali (2003): [ATR] value asymmetries and underlying vowel inventory structure

An underlying inventory with a tongue-root contrast is a 5Ht, 4Ht(H) or 4Ht(M) system according
to which heights carry the contrast; [Akan's nine vowels are 5Ht](##inventoryType?_akan) and
[Standard Yoruba's seven are 4Ht(M)](##inventoryType?_yoruba). The paper's survey of 110
Niger-Congo and Nilo-Saharan languages finds [+ATR] systematically dominant where high vowels
contrast and [−ATR] where only mid vowels do, and its last section derives the correlation from
lexical specification: only one value is present underlyingly, and the inventory decides which.
MAX([ATR]) and MAX([ATR])root preserve the specified value, *[ATR] penalizes it, and HARMONY
demands agreement. The rankings of these four constraints under which
[affixes take the root's value](##rootControl_iff) and under which
[the specified value wins from either position](##dominant_iff) are characterized, and under no
ranking does [the unspecified value override a specified root](##neutralizes_of_picksAt) unless
the contrast is lost, so that [a 4Ht(M) language with [+ATR] dominance](##yorubaPlus) is not
generated. A ban on [+ATR] low vowels above MAX([ATR]) gives
[indirect [−ATR] dominance](##reversal_optimal) before a low-vowel suffix.

## Implementation notes

* The [ATR] value is `Phonology.Feature.atr` read as `Bool`, `true` for [+ATR]. A contrast at a
  height is a [+ATR] vowel of that height whose [−ATR] twin is also in the inventory. The low
  vowel of the schematic inventories is the fragments' /a/.
* An underspecified representation is rendered by constraints that see only the specified value
  `s`: inputs and candidates are fully valued root–affix pairs, and a value is specified when it
  equals `s`. Every input has all four candidates.
* An affix outside any harmonic context is evaluated by *[ATR] and MAX([ATR]) alone
  (`affixSystem`), under the same ranking as the harmonic words.

## TODO

* The survey rows of the dominance tables and their counts, the criteria for telling 4Ht(H) from
  4Ht(M) systems and the genetic discussion are not formalized; with the rows, System-Dependent
  [ATR] Dominance would be a statement about each language's dominant value, with Kimatuumbi and
  Legbo the two languages the paper leaves unexplained.

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
  ∃ v ∈ I, P v ∧ v .atr = true ∧ v.setFeature .atr false ∈ I

instance (P : Segment → Prop) [DecidablePred P] : Decidable (HasContrastAmong I P) := by
  unfold HasContrastAmong; infer_instance

/-- The high vowels. -/
def IsHigh (v : Segment) : Prop := v .high = true

instance : DecidablePred IsHigh := fun v ↦ inferInstanceAs (Decidable (_ = _))

/-- The mid vowels. -/
def IsMid (v : Segment) : Prop := v .high = false ∧ v .low = false

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

-- (1a)
theorem nineVowel_eq : nineVowel = Akan.vowels := by decide

-- (1b)
theorem sevenVowelMid_eq : sevenVowelMid = Yoruba.vowels := by decide

-- (1)
theorem inventoryType?_schematic :
    inventoryType? nineVowel = some .fiveHeight ∧
      inventoryType? sevenVowelHigh = some .fourHeightHigh ∧
      inventoryType? sevenVowelMid = some .fourHeightMid ∧
      inventoryType? fiveVowel = none := by
  decide

-- Footnote 2: a missing front or back vowel leaves the type alone, as in Igbo, which lacks /ɛ/,
-- and Kaba, whose inventory is /i e a ɔ o u/.
theorem inventoryType?_erase :
    inventoryType? (nineVowel.erase (vowel .«ɛ»)) = some .fiveHeight ∧
      inventoryType? (sevenVowelMid.erase (vowel .«ɛ»)) = some .fourHeightMid := by
  decide

-- Akan's nine vowels form a 5Ht system.
theorem inventoryType?_akan : inventoryType? Akan.vowels = some .fiveHeight :=
  nineVowel_eq ▸ inventoryType?_schematic.1

-- Standard Yoruba's seven vowels form a 4Ht(M) system.
theorem inventoryType?_yoruba : inventoryType? Yoruba.vowels = some .fourHeightMid :=
  sevenVowelMid_eq ▸ inventoryType?_schematic.2.2.1

/-! ### System-Dependent [ATR] Dominance (20) -/

/-- The lexically specified [ATR] value is [+ATR] where high vowels contrast and [−ATR] where
only mid vowels do. By System-Dependent [ATR] Dominance (20) it is the systematically dominant
value. -/
def InventoryType.specifiedValue : InventoryType → Bool
  | .fiveHeight | .fourHeightHigh => true
  | .fourHeightMid => false

/-! ### Section 7: dominance from inventory-dependent specification

Only the specified value `s` is present underlyingly. MAX([ATR]) and its root-specific
version demand that specified input values survive; *[ATR] penalizes each specified value
on the surface; HARMONY demands agreement. -/

/-- The [ATR] values of a root and an affix. -/
structure Word where
  root  : Bool
  affix : Bool
  deriving DecidableEq, Fintype, Repr

/-- The four constraints of section 7. -/
inductive Con where
  /-- HARMONY requires root and affix to agree. -/
  | harmony
  /-- MAX([ATR])root requires a specified root value to survive. -/
  | maxRoot
  /-- *[ATR] assigns one violation per specified value on the surface. -/
  | starAtr
  /-- MAX([ATR]) requires every specified input value to survive, one violation per loss. -/
  | maxAtr
  deriving DecidableEq, Fintype

variable (s : Bool)

/-- The constraint system of a language whose specified value is `s`: an input is a root–affix
pair, its candidates the four fully valued pairs. -/
def system : ConstraintSystem Word Word Con where
  gen _ := Finset.univ
  con
    | .harmony => .binary fun p ↦ p.2.root ≠ p.2.affix
    | .maxRoot => .binary fun p ↦ p.1.root = s ∧ p.2.root ≠ s
    | .starAtr => fun p ↦ (if p.2.root = s then 1 else 0) + if p.2.affix = s then 1 else 0
    | .maxAtr => fun p ↦ (if p.1.root = s ∧ p.2.root ≠ s then 1 else 0) +
        if p.1.affix = s ∧ p.2.affix ≠ s then 1 else 0

variable {s} {r : Ranking Con}

private theorem picksAt_iff {w o : Word} : (system s).PicksAt r w o ↔ ∀ o', o' ≠ o →
    ∃ c, (system s).con c (w, o) < (system s).con c (w, o') ∧
      ∀ c', (system s).con c' (w, o') < (system s).con c' (w, o) → r.Dominates c c' := by
  simp [ConstraintSystem.picksAt_iff_exists_dominates, system]

/-- Affixes take the root's value, whatever the inputs, exactly under the rankings with HARMONY
and MAX([ATR])root above *[ATR] above MAX([ATR]): the ranking of tableaux (21) and (22). -/
theorem rootControl_iff :
    (∀ w, (system s).PicksAt r w ⟨w.root, w.root⟩) ↔
      r.Dominates .harmony .starAtr ∧ r.Dominates .maxRoot .starAtr ∧
        r.Dominates .starAtr .maxAtr := by
  constructor
  · intro h
    have h₁ : r.Dominates .harmony .starAtr := by
      obtain ⟨c, hc, hd⟩ := picksAt_iff.1 (h ⟨s, !s⟩) ⟨s, !s⟩ (by cases s <;> decide)
      cases s <;> cases c <;> first | exact absurd hc (by decide) | exact hd .starAtr (by decide)
    have h₃ : r.Dominates .starAtr .maxAtr := by
      obtain ⟨c, hc, hd⟩ := picksAt_iff.1 (h ⟨!s, s⟩) ⟨s, s⟩ (by cases s <;> decide)
      cases s <;> cases c <;> first | exact absurd hc (by decide) | exact hd .maxAtr (by decide)
    refine ⟨h₁, ?_, h₃⟩
    obtain ⟨c, hc, hd⟩ := picksAt_iff.1 (h ⟨s, !s⟩) ⟨!s, !s⟩ (by cases s <;> decide)
    cases s <;> cases c <;>
      first
        | exact absurd hc (by decide)
        | exact hd .starAtr (by decide)
        | exact absurd (hd .starAtr (by decide)) (asymm h₃)
  · rintro ⟨h₁, h₂, h₃⟩ ⟨wr, wa⟩
    have h₄ : r.Dominates .harmony .maxAtr := _root_.trans h₁ h₃
    have h₅ : r.Dominates .maxRoot .maxAtr := _root_.trans h₂ h₃
    refine picksAt_iff.2 fun ⟨or, oa⟩ ho' ↦ ?_
    cases s <;> cases wr <;> cases wa <;> cases or <;> cases oa <;>
      first
        | exact absurd rfl ho'
        | exact ⟨.harmony, by decide, fun c' hc' ↦ by
            cases c' <;> first | exact absurd hc' (by decide) | assumption⟩
        | exact ⟨.maxRoot, by decide, fun c' hc' ↦ by
            cases c' <;> first | exact absurd hc' (by decide) | assumption⟩
        | exact ⟨.starAtr, by decide, fun c' hc' ↦ by
            cases c' <;> first | exact absurd hc' (by decide) | assumption⟩

/-- The ranking of tableaux (21) and (22). -/
def rootControl : Ranking Con := .ofList [.harmony, .maxRoot, .starAtr, .maxAtr]

-- (21): /du-tI/ surfaces as [duti].
example : (system true).PicksAt rootControl ⟨true, false⟩ ⟨true, true⟩ := by decide

-- (22): /dU-ti/ surfaces as [dʊtɪ].
example : (system true).PicksAt rootControl ⟨false, true⟩ ⟨false, false⟩ := by decide

/-- A dominant system assigns the specified value when either input carries it. -/
def Word.dominantValue (s : Bool) (w : Word) : Bool := if w.root = s ∨ w.affix = s then s else !s

/-- The specified value wins from either position, the classic dominant pattern, exactly under
the rankings with HARMONY and MAX([ATR]) above *[ATR]. -/
theorem dominant_iff :
    (∀ w, (system s).PicksAt r w ⟨w.dominantValue s, w.dominantValue s⟩) ↔
      r.Dominates .harmony .starAtr ∧ r.Dominates .maxAtr .starAtr := by
  constructor
  · intro h
    constructor
    · obtain ⟨c, hc, hd⟩ := picksAt_iff.1 (h ⟨s, !s⟩) ⟨s, !s⟩ (by cases s <;> decide)
      cases s <;> cases c <;> first | exact absurd hc (by decide) | exact hd .starAtr (by decide)
    · obtain ⟨c, hc, hd⟩ := picksAt_iff.1 (h ⟨!s, s⟩) ⟨!s, !s⟩ (by cases s <;> decide)
      cases s <;> cases c <;> first | exact absurd hc (by decide) | exact hd .starAtr (by decide)
  · rintro ⟨h₁, h₂⟩ ⟨wr, wa⟩
    refine picksAt_iff.2 fun ⟨or, oa⟩ ho' ↦ ?_
    cases s <;> cases wr <;> cases wa <;> cases or <;> cases oa <;>
      first
        | exact absurd rfl ho'
        | exact ⟨.harmony, by decide, fun c' hc' ↦ by
            cases c' <;> first | exact absurd hc' (by decide) | assumption⟩
        | exact ⟨.maxAtr, by decide, fun c' hc' ↦ by
            cases c' <;> first | exact absurd hc' (by decide) | assumption⟩
        | exact ⟨.starAtr, by decide, fun c' hc' ↦ by
            cases c' <;> exact absurd hc' (by decide)⟩

-- With *[ATR] above both MAX constraints every specification is lost and the language has no
-- [ATR] contrast.
theorem neutralizes_iff :
    (∀ w, (system s).PicksAt r w ⟨!s, !s⟩) ↔
      r.Dominates .starAtr .maxRoot ∧ r.Dominates .starAtr .maxAtr := by
  constructor
  · intro h
    obtain ⟨c, hc, hd⟩ := picksAt_iff.1 (h ⟨s, !s⟩) ⟨s, s⟩ (by cases s <;> decide)
    cases s <;> cases c <;>
      first | exact absurd hc (by decide) | exact ⟨hd .maxRoot (by decide), hd .maxAtr (by decide)⟩
  · rintro ⟨h₁, h₂⟩ ⟨wr, wa⟩
    refine picksAt_iff.2 fun ⟨or, oa⟩ ho' ↦ ?_
    cases s <;> cases wr <;> cases wa <;> cases or <;> cases oa <;>
      first
        | exact absurd rfl ho'
        | exact ⟨.starAtr, by decide, fun c' hc' ↦ by
            cases c' <;> first | exact absurd hc' (by decide) | assumption⟩

/-- No ranking makes the unspecified value systematically dominant: if an unspecified affix
overrides a specified root, every word surfaces unspecified and the contrast is lost. -/
theorem neutralizes_of_picksAt (h : (system s).PicksAt r ⟨s, !s⟩ ⟨!s, !s⟩) (w : Word) :
    (system s).PicksAt r w ⟨!s, !s⟩ := by
  refine neutralizes_iff.2 ?_ w
  obtain ⟨c, hc, hd⟩ := picksAt_iff.1 h ⟨s, s⟩ (by cases s <;> decide)
  cases s <;> cases c <;>
    first | exact absurd hc (by decide) | exact ⟨hd .maxRoot (by decide), hd .maxAtr (by decide)⟩

/-- Yoruba⁺ is not generated: under the specification of Yoruba's inventory type, a ranking that
lets a [+ATR] affix advance a [−ATR] root makes every word [+ATR]. -/
theorem yorubaPlus : ∀ T ∈ inventoryType? Yoruba.vowels,
    (system T.specifiedValue).PicksAt r ⟨false, true⟩ ⟨true, true⟩ →
      ∀ w, (system T.specifiedValue).PicksAt r w ⟨true, true⟩ := by
  rw [inventoryType?_yoruba]
  rintro _ ⟨⟩
  exact neutralizes_of_picksAt

/-! ### Weak assimilatory dominance -/

variable (s) in
/-- A harmonizing affix in a context where harmony is inapplicable: *[ATR] and MAX([ATR]) alone
bear on its value. -/
def affixSystem : ConstraintSystem Bool Bool Con where
  gen _ := Finset.univ
  con
    | .starAtr => .binary fun p ↦ p.2 = s
    | .maxAtr => .binary fun p ↦ p.1 = s ∧ p.2 ≠ s
    | _ => 0

-- With *[ATR] above MAX([ATR]) the affix loses its specification and surfaces with the value
-- opposite to the specified one.
theorem affix_unspecified_iff :
    (∀ a, (affixSystem s).PicksAt r a !s) ↔ r.Dominates .starAtr .maxAtr := by
  simp only [ConstraintSystem.picksAt_iff_exists_dominates, affixSystem, Finset.mem_univ,
    true_and, forall_const]
  constructor
  · intro h
    obtain ⟨c, hc, hd⟩ := h s s (by cases s <;> decide)
    cases s <;> cases c <;> first | exact absurd hc (by decide) | exact hd .maxAtr (by decide)
  · intro h a o ho
    cases s <;> cases a <;> cases o <;>
      first
        | exact absurd rfl ho
        | exact ⟨.starAtr, by decide, fun c' hc' ↦ by
            cases c' <;> first | exact absurd hc' (by decide) | assumption⟩

-- With MAX([ATR]) above *[ATR] the affix keeps its value.
theorem affix_faithful_iff :
    (∀ a, (affixSystem s).PicksAt r a a) ↔ r.Dominates .maxAtr .starAtr := by
  simp only [ConstraintSystem.picksAt_iff_exists_dominates, affixSystem, Finset.mem_univ,
    true_and, forall_const]
  constructor
  · intro h
    obtain ⟨c, hc, hd⟩ := h s (!s) (by cases s <;> decide)
    cases s <;> cases c <;> first | exact absurd hc (by decide) | exact hd .starAtr (by decide)
  · intro h a o ho
    cases s <;> cases a <;> cases o <;>
      first
        | exact absurd rfl ho
        | exact ⟨.maxAtr, by decide, fun c' hc' ↦ by
            cases c' <;> first | exact absurd hc' (by decide) | assumption⟩
        | exact ⟨.starAtr, by decide, fun c' hc' ↦ by
            cases c' <;> exact absurd hc' (by decide)⟩

-- Weak assimilatory dominance: in a root-control language a harmonizing affix surfaces, outside
-- harmonic contexts, with the value opposite to the dominant one.
theorem affix_unspecified_of_rootControl
    (h : ∀ w, (system s).PicksAt r w ⟨w.root, w.root⟩) (a : Bool) :
    (affixSystem s).PicksAt r a !s :=
  affix_unspecified_iff.2 (rootControl_iff.1 h).2.2 a

-- Under the dominant ranking the affix stays faithful.
theorem affix_faithful_of_dominant
    (h : ∀ w, (system s).PicksAt r w ⟨w.dominantValue s, w.dominantValue s⟩) (a : Bool) :
    (affixSystem s).PicksAt r a a :=
  affix_faithful_iff.2 (dominant_iff.1 h).2 a

/-! ### Dominance reversal (23) -/

/-- An output for the input /tol-a/ of (23), a [+ATR] root with a [−ATR] low suffix in a
5Ht language, records the root's and the suffix's [ATR] values and the suffix's [low] value. -/
structure LowSuffixCand extends Word where
  low : Bool
  deriving DecidableEq, Repr

/-- Tableau (23) ranks *[+ATR, +low] and the preservation of [+low] above HARMONY above
MAX([ATR]), the last two those of a 5Ht system at the input, over [tola], [tɔla], [tolæ] and
[tole]. -/
def reversal : Tableau LowSuffixCand 4 :=
  Tableau.ofList
    {⟨⟨true, false⟩, true⟩, ⟨⟨false, false⟩, true⟩, ⟨⟨true, true⟩, true⟩, ⟨⟨true, true⟩, false⟩}
    [.binary fun c ↦ c.affix ∧ c.low, .binary fun c ↦ ¬ c.low,
      ((system InventoryType.fiveHeight.specifiedValue).conAt ⟨true, false⟩ .harmony).comap
        LowSuffixCand.toWord,
      ((system InventoryType.fiveHeight.specifiedValue).conAt ⟨true, false⟩ .maxAtr).comap
        LowSuffixCand.toWord]

/-- Indirect [−ATR] dominance: before the low-vowel suffix the [+ATR] root gives up its
specification, [tɔla]. -/
theorem reversal_optimal : reversal.optimal = {⟨⟨false, false⟩, true⟩} := by decide

end Casali2003
