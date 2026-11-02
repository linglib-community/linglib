/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Wordlist.Booij2019
public import Linglib.Morphology.ConstructionMorphology.Schema
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Booij (2019): The role of schemas in Construction Morphology

This file formalizes Booij's templatic and second-order schemas as schemas read through
subscriptings of their slots. The Damascus Arabic occupation schema (2) gives one root consonant
two slots, so its subscripting is not injective, and its instances are
[the words $C_1aC_2C_2aaC_3$](##occupation_instantiatesAt_iff).

A second-order schema is one description read through two subscriptings, one per sister, which
fill their coindexed variables alike. Javanese partial reduplication (13) pairs
[a reduplicant $C_1\text{ə}C_1y$ with the base $C_1y$](##reduplication_pairs_iff), and the Egyptian
Arabic comparative (16) pairs [an adjective $C_1VC_2VC_3$ with the comparative
$aC_1C_2aC_3$](##comparative_pairs_iff). Neither pairing is a product of a condition on each
sister, since *kibiir* pairs with *akbar* and *tixiin* with *atxan* but
[*kibiir* not with *atxan*](##comparative_ne_prod), and
[likewise for the reduplicants](##reduplication_ne_prod). No schema over single words, and so no
higher-order schema dominating the sisters, states the correspondence, which the coindexation
alone carries.

## Implementation notes

* The words are the CLDF forms of `Data/Wordlist/Booij2019.json`, read one segment per slot on
  the flat carrier by `CLDF.Wordlist.Form.slots`.
* A variable is a slot at `⊥`, which any segment fills, where Booij's `C` takes a consonant and
  `V` a vowel. His `y` ranges over sequences of sounds; here it is one slot, so the wordlist
  stores the residue of a Javanese base as one segment.
* Booij offers (2), after the unproductive Dutch diminutive verbs, as an example of the primarily
  motivating function of schemas, so its variables are closed; those of (13) and (16) are open.
* Only the phonological level of each schema is encoded, not the syntactic and semantic levels or
  the coindex that links the three.

## TODO

* Typed variables and sequence variables need slots that hold descriptions strictly between `⊥`
  and a segment, which `ConstructionMorphology.Schema.opens_subset` does not let be open.
* The higher-order schema (5) for Dutch *-er* and its four subschemas, the sister schemas (10)′,
  (11) and (14), the allomorphy schema (18), whose `f/s` and `v/z` are classes of segments, and
  the affixoid subschemas of Section 4.

## References

* [booij-2019]
-/

@[expose] public section

namespace Booij2019

open ConstructionMorphology

/-! ### The occupation template `C₁aC₂C₂aaC₃` -/

/-- The parts of the occupation template (2), three root consonants and two vowel constants. -/
inductive OccPart
  | c1 | c2 | c3 | a | aa
  deriving DecidableEq

/-- The occupation schema (2) pins the vowels and leaves the root consonants as closed
variables. -/
def occupation : Schema OccPart (Flat String) :=
  .nonproductive fun | .a => ↑"a" | .aa => ↑"aa" | _ => ⊥

/-- The six slots of `C₁aC₂C₂aaC₃` subscripted by parts, the second consonant occupying
two. -/
def occupationSub : Fin 6 → OccPart := ![.c1, .a, .c2, .c2, .aa, .c3]

/-- An item instantiates the occupation schema exactly when it is $C_1aC_2C_2aaC_3$ for some
consonants $C_1$, $C_2$ and $C_3$. -/
theorem occupation_instantiatesAt_iff {w : Fin 6 → Flat String} :
    occupation.InstantiatesAt occupationSub w ↔
      ∃ c₁ c₂ c₃, w = ![c₁, ↑"a", c₂, c₂, ↑"aa", c₃] := by
  refine ⟨fun ⟨u, hu, hw⟩ ↦ ⟨u .c1, u .c2, u .c3, ?_⟩, fun ⟨c₁, c₂, c₃, hw⟩ ↦ ?_⟩
  · have ha : u .a = ↑"a" := Flat.coe_le_iff.1 (hu .a)
    have haa : u .aa = ↑"aa" := Flat.coe_le_iff.1 (hu .aa)
    subst hw
    funext i
    fin_cases i <;> simp [occupationSub, ha, haa]
  · refine ⟨fun | .c1 => c₁ | .c2 => c₂ | .c3 => c₃ | .a => ↑"a" | .aa => ↑"aa",
      fun v ↦ by cases v <;> first | exact bot_le | exact le_rfl, ?_⟩
    subst hw
    funext i
    fin_cases i <;> rfl

-- (1)
theorem occupation_nouns :
    occupation.InstantiatesAt occupationSub Wordlist.xabbaaz.slots ∧
      occupation.InstantiatesAt occupationSub Wordlist.xaddaam.slots ∧
        occupation.InstantiatesAt occupationSub Wordlist.bawwaab.slots ∧
          occupation.InstantiatesAt occupationSub Wordlist.sammaak.slots := by
  decide

theorem not_occupation_of_ne_medial :
    ¬ occupation.InstantiatesAt occupationSub ![↑"x", ↑"a", ↑"b", ↑"d", ↑"aa", ↑"z"] := by
  decide

/-! ### Javanese partial reduplication -/

/-- The parts of the reduplication schema (13), which are the copied consonant, the schwa
constant, and the residue. -/
inductive RedPart
  | c1 | schwa | y
  deriving DecidableEq

/-- The reduplication schema (13) pins the schwa and leaves the consonant and residue open. -/
def reduplication : Schema RedPart (Flat String) :=
  .productive fun | .schwa => ↑"ə" | _ => ⊥

/-- The reduplicant `C₁əC₁y`, whose initial consonant occupies two slots. -/
def redSub : Fin 4 → RedPart := ![.c1, .schwa, .c1, .y]

/-- The base `C₁y`. -/
def baseSub : Fin 2 → RedPart := ![.c1, .y]

/-- A reduplicant and a base are paired by (13) exactly when they are $C_1\text{ə}C_1y$ and
$C_1y$ for one consonant $C_1$ and one residue $y$. -/
theorem reduplication_pairs_iff {r : Fin 4 → Flat String} {b : Fin 2 → Flat String} :
    reduplication.InstantiatesAt (Sum.elim redSub baseSub) (Sum.elim r b) ↔
      ∃ c y, r = ![c, ↑"ə", c, y] ∧ b = ![c, y] := by
  rw [Schema.instantiatesAt_elim_iff_exists]
  refine ⟨fun ⟨u, hu, hr, hb⟩ ↦ ⟨u .c1, u .y, ?_, ?_⟩, fun ⟨c, y, hr, hb⟩ ↦ ?_⟩
  · have hs : u .schwa = ↑"ə" := Flat.coe_le_iff.1 (hu .schwa)
    subst hr
    funext i
    fin_cases i <;> simp [redSub, hs]
  · subst hb
    funext i
    fin_cases i <;> rfl
  · refine ⟨fun | .c1 => c | .schwa => ↑"ə" | .y => y,
      fun v ↦ by cases v <;> first | exact bot_le | exact le_rfl, ?_, ?_⟩ <;>
      · subst_vars
        funext i
        fin_cases i <;> rfl

-- (12)
theorem reduplication_verbs :
    reduplication.InstantiatesAt (Sum.elim redSub baseSub)
        (Sum.elim Wordlist.tetamu.slots Wordlist.tamu.slots) ∧
      reduplication.InstantiatesAt (Sum.elim redSub baseSub)
        (Sum.elim Wordlist.jejawah.slots Wordlist.jawah.slots) ∧
      reduplication.InstantiatesAt (Sum.elim redSub baseSub)
        (Sum.elim Wordlist.gegeni.slots Wordlist.geni.slots) := by
  decide

/-- No condition on reduplicants and bases separately pairs them as (13) does, since
*tətamu* pairs with *tamu* and *jəjawah* with *jawah* but *tətamu* not with *jawah*. -/
theorem reduplication_ne_prod (R : Set (Fin 4 → Flat String)) (B : Set (Fin 2 → Flat String)) :
    {p | reduplication.InstantiatesAt (Sum.elim redSub baseSub) (Sum.elim p.1 p.2)} ≠ R ×ˢ B :=
  Schema.setOf_instantiatesAt_elim_ne_prod reduplication_verbs.1 reduplication_verbs.2.1
    (a := 0) (b := 0) rfl (by decide) R B

/-! ### The Egyptian Arabic comparative -/

/-- The parts of the comparative schema (16), which are three root consonants, the adjective's
two vowels, and the comparative's constant `a`. -/
inductive CmpPart
  | c1 | c2 | c3 | v1 | v2 | a
  deriving DecidableEq

/-- The comparative schema (16) pins the comparative vowel and leaves all else open. -/
def comparative : Schema CmpPart (Flat String) :=
  .productive fun | .a => ↑"a" | _ => ⊥

/-- The adjective template `C₁VC₂VC₃`. -/
def adjSub : Fin 5 → CmpPart := ![.c1, .v1, .c2, .v2, .c3]

/-- The comparative template `aC₁C₂aC₃`. -/
def cmpSub : Fin 5 → CmpPart := ![.a, .c1, .c2, .a, .c3]

/-- An adjective and a comparative are paired by (16) exactly when they are $C_1VC_2VC_3$ and
$aC_1C_2aC_3$ over the same three consonants. -/
theorem comparative_pairs_iff {p q : Fin 5 → Flat String} :
    comparative.InstantiatesAt (Sum.elim adjSub cmpSub) (Sum.elim p q) ↔
      ∃ c₁ c₂ c₃ v₁ v₂, p = ![c₁, v₁, c₂, v₂, c₃] ∧ q = ![↑"a", c₁, c₂, ↑"a", c₃] := by
  rw [Schema.instantiatesAt_elim_iff_exists]
  refine ⟨fun ⟨u, hu, hp, hq⟩ ↦ ⟨u .c1, u .c2, u .c3, u .v1, u .v2, ?_, ?_⟩,
    fun ⟨c₁, c₂, c₃, v₁, v₂, hp, hq⟩ ↦ ?_⟩
  · subst hp
    funext i
    fin_cases i <;> rfl
  · have ha : u .a = ↑"a" := Flat.coe_le_iff.1 (hu .a)
    subst hq
    funext i
    fin_cases i <;> simp [cmpSub, ha]
  · refine ⟨fun | .c1 => c₁ | .c2 => c₂ | .c3 => c₃ | .v1 => v₁ | .v2 => v₂ | .a => ↑"a",
      fun v ↦ by cases v <;> first | exact bot_le | exact le_rfl, ?_, ?_⟩ <;>
      · subst_vars
        funext i
        fin_cases i <;> rfl

-- (15)
theorem comparative_pairs :
    comparative.InstantiatesAt (Sum.elim adjSub cmpSub)
        (Sum.elim Wordlist.kibiir.slots Wordlist.akbar.slots) ∧
      comparative.InstantiatesAt (Sum.elim adjSub cmpSub)
        (Sum.elim Wordlist.tixiin.slots Wordlist.atxan.slots) ∧
        ¬ comparative.InstantiatesAt (Sum.elim adjSub cmpSub)
          (Sum.elim Wordlist.kibiir.slots Wordlist.atxan.slots) := by
  decide

/-- No condition on adjectives and comparatives separately pairs them as (16) does, so no schema
dominating the two sisters states the correspondence of their consonants. -/
theorem comparative_ne_prod (A B : Set (Fin 5 → Flat String)) :
    {p | comparative.InstantiatesAt (Sum.elim adjSub cmpSub) (Sum.elim p.1 p.2)} ≠ A ×ˢ B :=
  Schema.setOf_instantiatesAt_elim_ne_prod comparative_pairs.1 comparative_pairs.2.1
    (a := 0) (b := 1) rfl (by decide) A B

end Booij2019
