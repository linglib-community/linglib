/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Fintype.Order
public import Linglib.Data.Wordlist.Booij2019
public import Linglib.Morphology.ConstructionMorphology.Pattern
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.FinCases

/-!
# Booij (2019): The role of schemas in Construction Morphology

This file formalizes Booij's templatic and second-order schemas as patterns, rows of constants
and coindexed variables. The Damascus Arabic occupation schema (2) writes one root consonant
twice, and the words it subsumes are
[the words $C_1aC_2C_2aaC_3$](##occupation_le_iff).

A second-order schema is one pattern over the positions of two sisters, which fill their
coindexed variables alike. Javanese partial reduplication (13) pairs
[a reduplicant $C_1\text{ə}C_1y$ with the base $C_1y$](##reduplication_pairs_iff), and the Egyptian
Arabic comparative (16) pairs [an adjective $C_1VC_2VC_3$ with the comparative
$aC_1C_2aC_3$](##comparative_pairs_iff). Neither pairing is a product of a condition on each
sister, since *kibiir* pairs with *akbar* and *tixiin* with *atxan* but
[*kibiir* not with *atxan*](##comparative_ne_prod), and
[likewise for the reduplicants](##reduplication_ne_prod). No schema over single words, and so no
higher-order schema dominating the sisters, states the correspondence, which the coindexation
alone carries.

## Implementation notes

* The words are the CLDF forms of `Data/Wordlist/Booij2019.json`. The Arabic words are read one
  segment per slot by `slots`; the Javanese words are read by `baseOf` and `reduplicantOf`, whose
  slots hold sequences of segments, so that `y` takes the residue after the initial consonant.
* A variable is a slot at `⊥`, which any filler fills, where Booij's `C` takes a consonant and
  `V` a vowel.
* Only the phonological level of each schema is encoded, not the syntactic and semantic levels or
  the coindex that links the three, and not which variables are open to new fillers.

## TODO

* Typed variables need slots that hold descriptions strictly between `⊥` and a segment, which
  the flat order does not have.
* The higher-order schema (5) for Dutch *-er* and its four subschemas, the sister schemas (10)′,
  (11) and (14), the allomorphy schema (18), whose `f/s` and `v/z` are classes of segments, and
  the affixoid subschemas of Section 4.

## References

* [booij-2019]
-/

@[expose] public section

namespace Booij2019

open ConstructionMorphology Pattern CLDF.Wordlist

/-- The segments of a form read at `n` slots, with `⊥` past its end. -/
def slots {C : Type*} (n : ℕ) (f : Form C) (i : Fin n) : Flat String :=
  f.segments[i.val]?.elim ⊥ Flat.some

/-! ### The occupation template `C₁aC₂C₂aaC₃` -/

/-- (2): The occupation schema, three root consonants around two vowel constants, the second
consonant written twice. -/
abbrev occupation : Pattern (Fin 6) (Flat String) :=
  .ofTerms ![.inr 1, .inl "a", .inr 2, .inr 2, .inl "aa", .inr 3]

/-- A word instantiates the occupation schema exactly when it is $C_1aC_2C_2aaC_3$ for some
consonants $C_1$, $C_2$ and $C_3$. -/
theorem occupation_le_iff {g : Fin 6 → String} :
    occupation ≤ ofItem (Flat.some ∘ g) ↔ ∃ c₁ c₂ c₃, g = ![c₁, "a", c₂, c₂, "aa", c₃] := by
  refine ofTerms_le_ofItem_iff.trans ⟨fun ⟨x, hg⟩ ↦ ⟨x 1, x 2, x 3, ?_⟩,
    fun ⟨c₁, c₂, c₃, hg⟩ ↦ ⟨fun | 1 => c₁ | 2 => c₂ | _ => c₃, ?_⟩⟩ <;>
  · subst hg
    funext i
    fin_cases i <;> rfl

-- (1)
theorem occupation_nouns :
    ∀ f ∈ [Wordlist.xabbaaz, Wordlist.xaddaam, Wordlist.bawwaab, Wordlist.sammaak],
      occupation ≤ ofItem (slots 6 f) := by
  decide

theorem not_occupation_of_ne_medial :
    ¬ occupation ≤ ofItem ![↑"x", ↑"a", ↑"b", ↑"d", ↑"aa", ↑"z"] := by
  decide

/-! ### Javanese partial reduplication -/

/-- (13): The reduplication schema pairs the reduplicant `C₁əC₁y` with the base `C₁y`. Its slots
hold sequences of segments. -/
abbrev reduplication : Pattern (Fin 4 ⊕ Fin 2) (Flat (List String)) :=
  .ofTerms (Sum.elim ![.inr 1, .inl ["ə"], .inr 1, .inr 2] ![.inr 1, .inr 2])

/-- A base read as `C₁y`, its initial segment and the rest. -/
def baseOf {C : Type*} (f : Form C) : Fin 2 → Flat (List String) :=
  ![↑(f.segments.take 1), ↑(f.segments.drop 1)]

/-- A reduplicant read as `C₁əC₁y`, its first three segments one by one and the rest. -/
def reduplicantOf {C : Type*} (f : Form C) : Fin 4 → Flat (List String) :=
  ![↑(f.segments.take 1), ↑((f.segments.drop 1).take 1), ↑((f.segments.drop 2).take 1),
    ↑(f.segments.drop 3)]

/-- A reduplicant and a base are paired by (13) exactly when they are $C_1\text{ə}C_1y$ and
$C_1y$ for one consonant $C_1$ and one residue $y$. -/
theorem reduplication_pairs_iff {r : Fin 4 → List String} {b : Fin 2 → List String} :
    reduplication ≤ ofItem (Sum.elim (Flat.some ∘ r) (Flat.some ∘ b)) ↔
      ∃ c y, r = ![c, ["ə"], c, y] ∧ b = ![c, y] := by
  refine ofTerms_sumElim_le_ofItem_iff.trans ⟨fun ⟨x, hr, hb⟩ ↦ ⟨x 1, x 2, ?_, ?_⟩,
    fun ⟨c, y, hr, hb⟩ ↦ ⟨fun | 1 => c | _ => y, ?_, ?_⟩⟩ <;>
  · subst_vars
    funext i
    fin_cases i <;> rfl

-- (12)
theorem reduplication_verbs :
    reduplication ≤
        ofItem (Sum.elim (reduplicantOf Wordlist.tetamu) (baseOf Wordlist.tamu)) ∧
      reduplication ≤
        ofItem (Sum.elim (reduplicantOf Wordlist.jejawah) (baseOf Wordlist.jawah)) ∧
      reduplication ≤
        ofItem (Sum.elim (reduplicantOf Wordlist.gegeni) (baseOf Wordlist.geni)) :=
  ⟨by decide, by decide, by decide⟩

/-- No condition on reduplicants and bases separately pairs them as (13) does, since
*tətamu* pairs with *tamu* and *jəjawah* with *jawah* but *tətamu* not with *jawah*. -/
theorem reduplication_ne_prod (R : Set (Fin 4 → Flat (List String)))
    (B : Set (Fin 2 → Flat (List String))) :
    {(r, b) : (Fin 4 → Flat (List String)) × (Fin 2 → Flat (List String)) |
      reduplication ≤ ofItem (Sum.elim r b)} ≠ R ×ˢ B :=
  setOf_le_ofItem_sumElim_ne_prod reduplication_verbs.1 reduplication_verbs.2.1
    (a := 0) (b := 0) (by decide) (by decide) R B

/-! ### The Egyptian Arabic comparative -/

/-- (16): The comparative schema pairs the adjective `C₁VC₂VC₃` with the comparative
`aC₁C₂aC₃` over the same three consonants. -/
abbrev comparative : Pattern (Fin 5 ⊕ Fin 5) (Flat String) :=
  .ofTerms (Sum.elim ![.inr 1, .inr 4, .inr 2, .inr 5, .inr 3]
    ![.inl "a", .inr 1, .inr 2, .inl "a", .inr 3])

/-- An adjective and a comparative are paired by (16) exactly when they are $C_1VC_2VC_3$ and
$aC_1C_2aC_3$ over the same three consonants. -/
theorem comparative_pairs_iff {p q : Fin 5 → String} :
    comparative ≤ ofItem (Sum.elim (Flat.some ∘ p) (Flat.some ∘ q)) ↔
      ∃ c₁ c₂ c₃ v₁ v₂, p = ![c₁, v₁, c₂, v₂, c₃] ∧ q = !["a", c₁, c₂, "a", c₃] := by
  refine ofTerms_sumElim_le_ofItem_iff.trans
    ⟨fun ⟨x, hp, hq⟩ ↦ ⟨x 1, x 2, x 3, x 4, x 5, ?_, ?_⟩,
    fun ⟨c₁, c₂, c₃, v₁, v₂, hp, hq⟩ ↦
      ⟨fun | 1 => c₁ | 2 => c₂ | 3 => c₃ | 4 => v₁ | _ => v₂, ?_, ?_⟩⟩ <;>
  · subst_vars
    funext i
    fin_cases i <;> rfl

-- (15)
theorem comparative_pairs :
    comparative ≤ ofItem (Sum.elim (slots 5 Wordlist.kibiir) (slots 5 Wordlist.akbar)) ∧
      comparative ≤ ofItem (Sum.elim (slots 5 Wordlist.tixiin) (slots 5 Wordlist.atxan)) ∧
        ¬ comparative ≤
          ofItem (Sum.elim (slots 5 Wordlist.kibiir) (slots 5 Wordlist.atxan)) := by
  decide

/-- No condition on adjectives and comparatives separately pairs them as (16) does, so no schema
dominating the two sisters states the correspondence of their consonants. -/
theorem comparative_ne_prod (A B : Set (Fin 5 → Flat String)) :
    {(p, q) : (Fin 5 → Flat String) × (Fin 5 → Flat String) |
      comparative ≤ ofItem (Sum.elim p q)} ≠ A ×ˢ B :=
  setOf_le_ofItem_sumElim_ne_prod comparative_pairs.1 comparative_pairs.2.1
    (a := 0) (b := 1) (by decide) (by decide) A B

end Booij2019
