module

public import Linglib.Syntax.Reflex
public import Linglib.Fragments.Mayan.Extraction
public import Linglib.Fragments.Mayan.Mam.Voice

/-!
# Mam extraction marking

Mam (Mamean Mayan) has no Agent Focus form. In every dialect but possibly two, a transitive
subject is extracted by putting the verb in the antipassive *-n*, so that the argument extracted
is an absolutive one; the antipassive is the Mam response to the Mayan ban on extracting an
ergative argument. San Juan Ostuncalco Mam further marks the extraction of a recipient, which
like a benefactive is introduced by the relational noun *e*, or of an adjunct with the movement
enclitic =(y)a', which may attach to the verbal complex and to a directional auxiliary when the
clause has one, each optionally. Recipients, instruments, benefactives, locatives, reasons,
purposes and manners license the enclitic; temporals do not, and absolutive extraction is
unmarked.

## Main declarations

* `Mam.Extraction.movementEnclitic`: the enclitic =(y)a'.
* `Mam.Extraction.realize`: the reflexes extraction from each `Mayan.ExtractionSite` licenses,
  the antipassive's marker taken from `Mam.antipassive`.

## Main results

* `Mam.Extraction.antipassive_mem_realize_iff`: the antipassive is the reflex of
  transitive-subject extraction alone.
* `Mam.Extraction.enclitic_mem_realize_argument_iff`: among the arguments, the recipient alone
  licenses the enclitic.
* `Mam.Extraction.enclitic_directional_mem_realize_iff`: the directional hosts the enclitic at
  exactly the sites the verbal complex does.

## Implementation notes

The distribution of the enclitic across clause sizes and movement paths is formalized in
`Studies/ElkinsTorrenceBrown2026.lean`.

## References

* [aissen-2017b]
* [elkins-torrence-brown-2026]
* [england-1989]
* [england-2017]
-/

@[expose] public section

namespace Mam.Extraction

/-- The movement enclitic =(y)a'. -/
def movementEnclitic : Morphology.Morph := .encl "(y)a'"

/-- Transitive-subject extraction antipassivizes the verb; extraction of the recipient or of an
adjunct of any class but the temporals licenses =(y)a' on the verbal complex and on a
directional, each optional and independent of the other; absolutive and temporal extraction are
unmarked. -/
def realize : Mayan.ExtractionSite → Finset (Reflex Mayan.Host)
  | .argument .A => {.morpheme .verb antipassive.marker}
  | .argument .R | .adjunct .instrument | .adjunct .benefactive | .adjunct .locative
  | .adjunct .reason | .adjunct .purpose | .adjunct .manner =>
      {.morpheme .verbalComplex [movementEnclitic], .morpheme .directional [movementEnclitic]}
  | _ => ∅

@[simp] theorem realize_argument_A :
    realize (.argument .A) = {.morpheme .verb antipassive.marker} := rfl

@[simp] theorem realize_adjunct_temporal : realize (.adjunct .temporal) = ∅ := rfl

theorem realize_argument_eq_empty_iff (r : ArgumentRole) :
    realize (.argument r) = ∅ ↔ r ≠ .A ∧ r ≠ .R := by
  decide +revert

theorem realize_adjunct_of_ne_temporal {a : Mayan.Adjunct} (h : a ≠ .temporal) :
    realize (.adjunct a) =
      {.morpheme .verbalComplex [movementEnclitic], .morpheme .directional [movementEnclitic]} := by
  decide +revert

theorem realize_adjunct_nonempty_iff (a : Mayan.Adjunct) :
    (realize (.adjunct a)).Nonempty ↔ a ≠ .temporal := by
  decide +revert

theorem antipassive_mem_realize_iff (s : Mayan.ExtractionSite) :
    Reflex.morpheme .verb antipassive.marker ∈ realize s ↔ s = .argument .A := by
  decide +revert

theorem enclitic_mem_realize_argument_iff (r : ArgumentRole) :
    Reflex.morpheme .verbalComplex [movementEnclitic] ∈ realize (.argument r) ↔ r = .R := by
  decide +revert

theorem enclitic_directional_mem_realize_iff (s : Mayan.ExtractionSite) :
    Reflex.morpheme .directional [movementEnclitic] ∈ realize s ↔
      Reflex.morpheme .verbalComplex [movementEnclitic] ∈ realize s := by
  decide +revert

theorem isOvert_of_mem_realize (s : Mayan.ExtractionSite) : ∀ ρ ∈ realize s, ρ.IsOvert := by
  decide +revert

end Mam.Extraction
