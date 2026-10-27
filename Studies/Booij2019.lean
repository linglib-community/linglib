/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Wordlist.Booij2019
public import Linglib.Morphology.ConstructionMorphology.Schema
public import Linglib.Morphology.Morphotactics.TemplateMatch
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Booij (2019): The role of schemas in Construction Morphology

This file formalizes Booij's templatic and second-order schemas as coindexed schemas
read through subscriptings of template slots. A templatic schema is a description over root
consonants and vowel constants, and a consonant that occupies two slots, the gemination of the
Damascus Arabic occupation template `C₁aC₂C₂aaC₃` of (2), is a subscripting that is not
injective: an item instantiates the schema exactly when its vowels are the template's and the
two geminate slots are filled alike (`occupation_instantiatesAt_iff`). The subscripting is the
association of the autosegmental template: the slots it coindexes are the slots associated
to one melody element (`occupationSub_eq_iff_assoc_eq`), and the association spells out the
word (`xabbaazMatch_spellout`).

Second-order schemas relate two templates over one root. Javanese partial reduplication (13)
copies the initial consonant into the reduplicant, so the reduplicant repeats one variable and
shares it with the base (`reduplication_pairs_iff`); the Egyptian Arabic comparative (16) pairs
an adjective with the comparative template over the same three consonants
(`comparative_pairs_iff`), so *kibiir* pairs with *akbar* and not with *atxan*.

## Implementation notes

* The words are the CLDF forms of `Data/Wordlist/Booij2019.json`, read as slot-indexed segments
  on the flat carrier by `CLDF.Wordlist.Form.slots`; slots are `Fin n` positions. A variable
  standing for a sequence of sounds, the paper's `y`, is one segment holding the residue.
* The higher-order schema for Dutch *-er* and the affixoid discussion are not formalized.

## References

* [booij-2019]
* [mccarthy-1981]
-/

@[expose] public section

namespace Booij2019

open Morphology ConstructionMorphology

/-! ### The occupation template `C₁aC₂C₂aaC₃` -/

/-- The parts of the occupation template (2), three root consonants and two vowel constants. -/
inductive OccPart
  | c1 | c2 | c3 | a | aa
  deriving DecidableEq

/-- The occupation schema (2) pins the vowels and leaves the root consonants open. -/
def occupation : Schema OccPart (Flat String) :=
  ⟨fun | .a => ↑"a" | .aa => ↑"aa" | _ => ⊥, {.c1, .c2, .c3}⟩

/-- The six slots of `C₁aC₂C₂aaC₃` subscripted by parts, the second consonant occupying
two. -/
def occupationSub : Fin 6 → OccPart := ![.c1, .a, .c2, .c2, .aa, .c3]

/-- An item instantiates the occupation schema exactly when its vowels are the template's and
the two slots of the second consonant are filled alike, since gemination is a subscripting that
is not injective. -/
theorem occupation_instantiatesAt_iff {w : Fin 6 → Flat String} :
    occupation.InstantiatesAt occupationSub w ↔
      w 1 = ↑"a" ∧ w 4 = ↑"aa" ∧ w 2 = w 3 := by
  rw [Schema.instantiatesAt_iff]
  constructor
  · rintro ⟨hc, hf⟩
    exact ⟨Flat.coe_le_iff.1 (hc 1), Flat.coe_le_iff.1 (hc 4), hf (by decide)⟩
  · rintro ⟨h1, h4, h23⟩
    refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · fin_cases i <;> first | exact bot_le | exact h1.ge | exact h4.ge
    · fin_cases i <;> fin_cases j <;>
        first | rfl | exact h23 | exact h23.symm | exact absurd hij (by decide)

-- (1)
theorem occupation_nouns :
    occupation.InstantiatesAt occupationSub Wordlist.xabbaaz.slots ∧
      occupation.InstantiatesAt occupationSub Wordlist.xaddaam.slots ∧
        occupation.InstantiatesAt occupationSub Wordlist.bawwaab.slots ∧
          occupation.InstantiatesAt occupationSub Wordlist.sammaak.slots := by
  simp only [occupation_instantiatesAt_iff]
  decide

theorem not_occupation_of_ne_medial :
    ¬ occupation.InstantiatesAt occupationSub
      ![↑"x", ↑"a", ↑"b", ↑"d", ↑"aa", ↑"z"] := by
  rw [occupation_instantiatesAt_iff]
  decide

/-! ### The subscripting as autosegmental association -/

/-- The template of (2) as a CV skeleton. -/
def occupationTemplate : Autosegmental.Skeleton := [.C, .V, .C, .C, .V, .C]

/-- *xabbaaz* as the association of the root /x b z/ and the vocalism /a aa/ to the template,
in which the second root consonant is associated to two slots. -/
def xabbaazMatch : TemplateMatch String where
  root := ⟨["x", "b", "z"]⟩
  vocalism := ["a", "aa"]
  template := occupationTemplate
  associations :=
    [⟨.root, 0, 0⟩, ⟨.vocalism, 0, 1⟩, ⟨.root, 1, 2⟩, ⟨.root, 1, 3⟩,
      ⟨.vocalism, 1, 4⟩, ⟨.root, 2, 5⟩]

/-- The melody element a slot is associated to. -/
def xabbaazAssoc (i : Fin 6) : Option (AssocSource × Nat) :=
  (xabbaazMatch.associations.find? (·.slotIndex == i.val)).map fun a ↦ (a.source, a.melodyIndex)

/-- The association lines spell out *xabbaaz*. -/
theorem xabbaazMatch_spellout : xabbaazMatch.spellout = Wordlist.xabbaaz.segments := by
  decide

/-- The subscripting and the association agree, as two slots carry the same part exactly when
they are associated to the same melody element. -/
theorem occupationSub_eq_iff_assoc_eq (i j : Fin 6) :
    occupationSub i = occupationSub j ↔ xabbaazAssoc i = xabbaazAssoc j := by
  fin_cases i <;> fin_cases j <;> decide

/-! ### Javanese partial reduplication -/

/-- The parts of the reduplication schema (13), which are the copied consonant, the schwa
constant, and the residue. -/
inductive RedPart
  | c1 | schwa | y
  deriving DecidableEq

/-- The reduplication schema (13) pins the schwa and leaves the consonant and residue open. -/
def reduplication : Schema RedPart (Flat String) :=
  ⟨fun | .schwa => ↑"ə" | _ => ⊥, {.c1, .y}⟩

/-- The reduplicant `C₁əC₁y`, whose initial consonant occupies two slots. -/
def redSub : Fin 4 → RedPart := ![.c1, .schwa, .c1, .y]

/-- The base `C₁y`. -/
def baseSub : Fin 2 → RedPart := ![.c1, .y]

/-- A reduplicant and base instantiate (13) iff the reduplicant has the schwa, copies its initial
consonant, and shares consonant and residue with the base. -/
theorem reduplication_pairs_iff {r : Fin 4 → Flat String} {b : Fin 2 → Flat String} :
    reduplication.InstantiatesAt (Sum.elim redSub baseSub) (Sum.elim r b) ↔
      r 1 = ↑"ə" ∧ r 0 = r 2 ∧ r 0 = b 0 ∧ r 3 = b 1 := by
  rw [Schema.instantiatesAt_elim_iff]
  constructor
  · rintro ⟨hr, -, hf, -, h⟩
    exact ⟨Flat.coe_le_iff.1 (hr 1), hf (by decide), h 0 0 (by decide), h 3 1 (by decide)⟩
  · rintro ⟨h1, h02, h0, h3⟩
    refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun i j hij ↦ ?_, fun i j hij ↦ ?_, fun i j hij ↦ ?_⟩
    · fin_cases i <;> first | exact bot_le | exact h1.ge
    · fin_cases i <;> exact bot_le
    · fin_cases i <;> fin_cases j <;>
        first | rfl | exact h02 | exact h02.symm | exact absurd hij (by decide)
    · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
    · fin_cases i <;> fin_cases j <;>
        first | exact h0 | exact h02.symm.trans h0 | exact h3 | exact absurd hij (by decide)

-- (12)
theorem reduplication_verbs :
    reduplication.InstantiatesAt (Sum.elim redSub baseSub)
        (Sum.elim Wordlist.tetamu.slots Wordlist.tamu.slots) ∧
      reduplication.InstantiatesAt (Sum.elim redSub baseSub)
        (Sum.elim Wordlist.jejawah.slots Wordlist.jawah.slots) ∧
      reduplication.InstantiatesAt (Sum.elim redSub baseSub)
        (Sum.elim Wordlist.gegeni.slots Wordlist.geni.slots) := by
  simp only [reduplication_pairs_iff]
  decide

/-! ### The Egyptian Arabic comparative -/

/-- The parts of the comparative schema (16), which are three root consonants, the adjective's
two open vowels, and the comparative's constant `a`. -/
inductive CmpPart
  | c1 | c2 | c3 | v1 | v2 | a
  deriving DecidableEq

/-- The comparative schema (16) pins the comparative vowel and leaves all else open. -/
def comparative : Schema CmpPart (Flat String) :=
  ⟨fun | .a => ↑"a" | _ => ⊥, {.c1, .c2, .c3, .v1, .v2}⟩

/-- The adjective template `C₁VC₂VC₃`. -/
def adjSub : Fin 5 → CmpPart := ![.c1, .v1, .c2, .v2, .c3]

/-- The comparative template `aC₁C₂aC₃`. -/
def cmpSub : Fin 5 → CmpPart := ![.a, .c1, .c2, .a, .c3]

/-- An adjective and a comparative are a paired instantiation of (16) exactly when the
comparative has its vowels and the two share their three consonants. -/
theorem comparative_pairs_iff {p q : Fin 5 → Flat String} :
    comparative.InstantiatesAt (Sum.elim adjSub cmpSub) (Sum.elim p q) ↔
      q 0 = ↑"a" ∧ q 3 = ↑"a" ∧ p 0 = q 1 ∧ p 2 = q 2 ∧ p 4 = q 4 := by
  rw [Schema.instantiatesAt_elim_iff]
  constructor
  · rintro ⟨-, hq, -, -, h⟩
    exact ⟨Flat.coe_le_iff.1 (hq 0), Flat.coe_le_iff.1 (hq 3), h 0 1 (by decide),
      h 2 2 (by decide), h 4 4 (by decide)⟩
  · rintro ⟨h0, h3, h01, h22, h44⟩
    refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun i j hij ↦ ?_, fun i j hij ↦ ?_, fun i j hij ↦ ?_⟩
    · fin_cases i <;> exact bot_le
    · fin_cases i <;> first | exact bot_le | exact h0.ge | exact h3.ge
    · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
    · fin_cases i <;> fin_cases j <;>
        first | rfl | exact h0.trans h3.symm | exact h3.trans h0.symm | exact absurd hij (by decide)
    · fin_cases i <;> fin_cases j <;>
        first | exact h01 | exact h22 | exact h44 | exact absurd hij (by decide)

theorem comparative_pairs :
    comparative.InstantiatesAt (Sum.elim adjSub cmpSub)
        (Sum.elim Wordlist.kibiir.slots Wordlist.akbar.slots) ∧
      comparative.InstantiatesAt (Sum.elim adjSub cmpSub)
        (Sum.elim Wordlist.tixiin.slots Wordlist.atxan.slots) ∧
        ¬ comparative.InstantiatesAt (Sum.elim adjSub cmpSub)
          (Sum.elim Wordlist.kibiir.slots Wordlist.atxan.slots) := by
  simp only [comparative_pairs_iff]
  decide

end Booij2019
