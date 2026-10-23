module

public import Linglib.Data.WALS.Features.F106A
public import Linglib.Syntax.Reciprocal
public import Linglib.Fragments.English.Reciprocals
public import Linglib.Fragments.German.Reciprocals
public import Linglib.Fragments.Greek.StandardModern.Reciprocals
public import Linglib.Fragments.Greek.StandardModern.Voice
public import Linglib.Fragments.Romance.French.Clitics
public import Linglib.Fragments.Romance.French.Reciprocals
public import Linglib.Fragments.Romance.Spanish.Clitics
public import Linglib.Fragments.Romance.Spanish.Reciprocals
public import Linglib.Fragments.Slavic.Russian.Reciprocals
public import Linglib.Fragments.Slavic.Russian.Voice
public import Linglib.Fragments.Swahili.Reciprocals
public import Linglib.Fragments.Wambaya.Reciprocals
public import Linglib.Fragments.Wambaya.Voice

/-!
# Maslova and Nedjalkov (2013): Reciprocal Constructions

[maslova-nedjalkov-2013] classify languages by the polysemy of their non-iconic reciprocal
constructions (§2). A reciprocal construction either can also express the reflexive meaning or
cannot, so a language has reflexive reciprocal constructions, non-reflexive ones, both (the mixed
type), or no non-iconic reciprocal construction at all. A construction expresses the reflexive
meaning when its form is that of a reflexive construction, so the value is where the forms of a
language's reciprocal markers lie against the forms of its reflexive exponents: all among them,
none, some, or no markers at all (`ofInventory` and its characterizations, such as
`ofInventory_eq_mixed_iff`). The chapter's own examples come out as it states, English with only
non-reflexive reciprocals and German of the mixed type (`ofInventory_english`,
`ofInventory_german`, §2.2), and every language of the chapter's sample whose reciprocal and
reflexive exponents the fragments record has the value the chapter codes (`ofInventory_eq_wals`).

## Implementation notes

The reflexive exponents are the fragments' reflexive pronouns, clitics, prefixes and voice
markers, compared with the reciprocal markers by form. Identity of form does not tell polysemy
from accidental homophony, and the chapter's criterion is the same formal one. Mandarin, coded
non-reflexive, is left out of `Language`: its fragment's one marker, the compound *dǎ-lái-dǎ-qù*,
repeats its verb, the iconic encoding the chapter sets aside (§2.1).

## TODO

`ofInventory` reads every marker of an inventory, while the chapter counts only the non-iconic
constructions; `Reciprocal.Strategy` would need to record iconicity for the value to be exact.

## References

* [E. Maslova and V. P. Nedjalkov, *Reciprocal Constructions* (2013)][maslova-nedjalkov-2013]
-/

@[expose] public section

namespace MaslovaNedjalkov2013

open Reciprocal Data.WALS.F106A

/-! ### The value of an inventory -/

/-- The value of an inventory of reciprocal markers against a language's reflexive forms `F`:
identical to the reflexive when every marker's form is among them, distinct when none is, mixed
when some are, and no reciprocal construction for an empty inventory. -/
def ofInventory (inv : Finset Marker) (F : Finset (List Morphology.Morph)) : ReciprocalType :=
  if inv = ∅ then .noReciprocalConstruction
  else if inv.image (·.morphs) ⊆ F then .identicalToReflexive
  else if Disjoint (inv.image (·.morphs)) F then .distinctFromReflexive
  else .mixed

variable {inv : Finset Marker} {F : Finset (List Morphology.Morph)}

theorem not_disjoint_of_subset (h₀ : inv ≠ ∅) (h : inv.image (·.morphs) ⊆ F) :
    ¬ Disjoint (inv.image (·.morphs)) F :=
  fun hd ↦ h₀ (Finset.image_eq_empty.mp (Finset.disjoint_self_iff_empty _ |>.mp (hd.mono_right h)))

@[simp]
theorem ofInventory_eq_noReciprocalConstruction_iff :
    ofInventory inv F = .noReciprocalConstruction ↔ inv = ∅ := by
  unfold ofInventory; split_ifs <;> simp_all

@[simp]
theorem ofInventory_eq_identicalToReflexive_iff :
    ofInventory inv F = .identicalToReflexive ↔ inv ≠ ∅ ∧ inv.image (·.morphs) ⊆ F := by
  unfold ofInventory; split_ifs <;> simp_all

@[simp]
theorem ofInventory_eq_distinctFromReflexive_iff :
    ofInventory inv F = .distinctFromReflexive ↔
      inv ≠ ∅ ∧ Disjoint (inv.image (·.morphs)) F := by
  unfold ofInventory
  split_ifs with h₀ h₁ h₂ <;> simp_all [not_disjoint_of_subset]

@[simp]
theorem ofInventory_eq_mixed_iff :
    ofInventory inv F = .mixed ↔
      ¬ inv.image (·.morphs) ⊆ F ∧ ¬ Disjoint (inv.image (·.morphs)) F := by
  unfold ofInventory
  split_ifs with h₀ h₁ h₂ <;> simp_all

/-! ### The sample -/

/-- The languages of the chapter's sample whose reciprocal markers a fragment records. -/
inductive Language where
  | english | french | german | greek | russian | spanish | swahili | wambaya
  deriving DecidableEq

/-- The WALS code under which the chapter's data lists the language. -/
def Language.walsCode : Language → String
  | .english => "eng" | .french => "fre" | .german => "ger" | .greek => "grk"
  | .russian => "rus" | .spanish => "spa" | .swahili => "swa" | .wambaya => "wam"

/-- The language's reciprocal markers, from its fragment. -/
def Language.markers : Language → Finset Marker
  | .english => English.Reciprocals.markers
  | .french => French.Reciprocals.markers
  | .german => German.Reciprocals.markers
  | .greek => Greek.StandardModern.Reciprocals.markers
  | .russian => Russian.Reciprocals.markers
  | .spanish => Spanish.Reciprocals.markers
  | .swahili => Swahili.Reciprocals.markers
  | .wambaya => Wambaya.Reciprocals.markers

/-- The forms of the language's reflexive exponents, taken from its fragments, are those of its
reflexive pronouns and clitics as free forms, the Swahili object-slot prefix, and the markers of
its reflexive voices. -/
def Language.reflexives : Language → Finset (List Morphology.Morph)
  | .english => English.Pronouns.reflexives.image fun r ↦ [.free r.form]
  | .french => {[.free French.Clitics.se.form]}
  | .german => {[.free German.Pronouns.sich.form]}
  | .greek => {Greek.StandardModern.reflexive.marker}
  | .russian => {Russian.reflexive.marker, [.free Russian.Reciprocals.sebja.form]}
  | .spanish => Spanish.Clitics.reflexive.image fun r ↦ [.free r.form]
  | .swahili => {[Swahili.Reciprocals.reflexivePrefix]}
  | .wambaya => {Wambaya.reflexive.marker}

/-! ### The chapter's examples (§2.2) -/

theorem ofInventory_english :
    ofInventory English.Reciprocals.markers (Language.reflexives .english) =
      .distinctFromReflexive := by
  decide

theorem ofInventory_german :
    ofInventory German.Reciprocals.markers (Language.reflexives .german) = .mixed := by
  decide

/-! ### The coding -/

theorem ofInventory_eq_wals (l : Language) :
    allData.lookup l.walsCode = some (ofInventory l.markers l.reflexives) := by
  cases l <;> decide +kernel

end MaslovaNedjalkov2013
