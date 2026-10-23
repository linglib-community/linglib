module

public import Linglib.Syntax.Voice.Basic
public import Linglib.Fragments.Dargwa.Tanti.Locatives

/-!
# Tanti Dargwa voice

This file defines the valency alternations of Tanti Dargwa as Sumbatova describes them. The
causative *-aq* is the only valency-changing morphology: the causee of an intransitive base is
the absolutive P of the derived clause, that of a transitive base an oblique in the
inter-elative, a locative form without the direction marker every spatial elative carries. The
antipassive is uncoded and confined to imperfective forms, and some transitive forms are
P-labile, the preterite *če-b-asː-un* meaning 'he glued it' or 'it stuck' where the future
tells the two apart by its thematic suffix.

## Main definitions

* `Dargwa.Tanti.causativeOfIntransitive`, `Dargwa.Tanti.causativeOfTransitive`,
  `Dargwa.Tanti.alternations`: the causatives, and the valency alternations
* `Dargwa.Tanti.causeeForm`: the inter-elative of the causee of a transitive base

## Main results

* `Dargwa.Tanti.isCoded_iff`: the two causatives are the alternations coded on the verb
* `Dargwa.Tanti.causativeOfIntransitive_fateOfRole_S`, `Dargwa.Tanti.causativeOfTransitive_valency`:
  the causee of an intransitive base stays a core term; that of a transitive base is demoted as the
  causer is introduced, so the valency is unchanged
* `Dargwa.Tanti.not_isSpatial_causeeForm`, `Dargwa.Tanti.causeeForm_morphs`: the causee form is the
  directionless elative no spatial form is, *-cːe-r* after the oblique stem
* `Dargwa.Tanti.labile_future_thematic`: the future forms of a P-labile verb differ in their
  thematic suffix

## Implementation notes

* The demoted causee and the antipassive patient are adpositional positions of the derived
  frame, the frame vocabulary's oblique; the case each takes is stated with the voice.

## TODO

* That the antipassive is confined to imperfective forms needs an aspectual restriction `Voice`
  does not have; that its demoted P is an ergative controlling no agreement is not stated.

## References

* [N. Sumbatova, *Dargwa* (2021)][sumbatova-2021]
* [D. Creissels, *Transitivity, Valency, and Voice* (2024)][creissels-2024]
-/

@[expose] public section

namespace Dargwa.Tanti

open ArgumentFrame.Slot Morphology

/-- The causative *-aq* of an intransitive verb. The causer is the ergative A and the causee,
the initial S, the absolutive P. -/
def causativeOfIntransitive : Voice := Voice.causative.marked [.suff "aq"]

/-- The causative *-aq* of a transitive verb. The causer is the ergative A and the causee, the
initial A, an oblique in the inter-elative. -/
def causativeOfTransitive : Voice :=
  (Voice.of .np ⟨some .nominal, [.nominal, .adpositional]⟩
    [some (complement 1), some (complement 0), some external]).marked [.suff "aq"]

/-- The inter-elative of the causee of a transitive base, a locative form without a direction
marker. -/
def causeeForm : LocativeForm := ⟨.inter, .elative, none⟩

/-- The valency alternations of Tanti: the uncoded antipassive, the uncoded anticausative of a
P-labile verb, and the two causatives. -/
def alternations : Finset Voice :=
  {.antipassive, .anticausative, causativeOfIntransitive, causativeOfTransitive}

theorem isCoded_iff {v : Voice} (hv : v ∈ alternations) :
    v.IsCoded ↔ v = causativeOfIntransitive ∨ v = causativeOfTransitive := by
  simp only [alternations, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> decide

theorem causativeOfIntransitive_fateOfRole_S :
    causativeOfIntransitive.fateOfRole .S = .maintained := by decide

theorem causativeOfTransitive_valency :
    causativeOfTransitive.Nucleativizes ∧
      causativeOfTransitive.fateOfRole .A = .denucleativized ∧
      causativeOfTransitive.derived.valency = causativeOfTransitive.initial.valency := by
  decide

theorem not_isSpatial_causeeForm : ¬ causeeForm.IsSpatial :=
  LocativeForm.not_isSpatial_elative_none _

theorem causeeForm_morphs (g : Gender.Marker) :
    causeeForm.morphs g = [.suff "cːe", .suff "r"] := rfl

theorem labile_future_thematic :
    thematic ⟨.third, .third⟩ = .suff "u" ∧ .suff "ar" ∈ intransitiveThematic .third := by
  decide

end Dargwa.Tanti
