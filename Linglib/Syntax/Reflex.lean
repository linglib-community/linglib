/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Basic
public import Linglib.Morphology.Morph

/-!
# Overt reflexes of a designated constituent

A grammar leaves perceptible traces of a constituent's designated status: of a focus, of an
A′-extraction site, of an intermediate landing site of successive-cyclic movement. A `Reflex` is a
perceptible perturbation at a host constituent: a displaced exponent, a morpheme with its marker,
a phrase edge, or metrical prominence. A marking system assigns each designated target its finite
set of reflexes. Reflexes classify by `Reflex.Modality` and further by `Reflex.Channel`, the
phonological, morphological and syntactic cut. Like `Judgment` for acceptability, this is a
vocabulary for what a theory predicts: studies translate their predictions into it, and no theory
consumes it as machinery.

## Main declarations

* `Reflex`: the four kinds of reflex, `Reflex.morpheme` carrying its marker as a list of morphs
  so that one morpheme at two hosts is one marker twice.
* `Reflex.IsOvert`: a morpheme reflex has a nonempty marker.
* `Reflex.Perceptible`: every designated target of a marking system receives a reflex.
* `Reflex.PiedPipes`, `Reflex.AntiPiedPipes`, `Reflex.ExactlyTargets`: Branan and Erlewine's
  three configurations of host and target in the containment order.
* `Reflex.ExactlyTargets.piedPipes_iff`, `Reflex.ExactlyTargets.antiPiedPipes_iff`: reflexes
  sharing a host relate to a target as the host does.

## Implementation notes

* Only perceptible alternants are reflexes. A string-vacuous operation (Hausa subject fronting)
  contributes none, a default exponent surfacing whatever the designation (the Wolof expletive
  *l-*) is not one since reflexes covary with the target, and zero is never one, covert marking
  being exponence-side competition, which `IsOvert` states of a morpheme reflex. Deletion of
  otherwise expected material (Malay voice-marker deletion) is a reflex. Semantic reflexes of
  movement (intermediate scope, reconstruction) are interpretation facts left to their studies.
* The marker of a morpheme reflex is the list of morphs coding it, as `Voice.marker` codes a
  voice, so a fragment whose reflex is a voice alternation passes the voice's marker through. A
  paradigm alternation with no segmentable exponent, such as the Hausa relative form of the
  person–aspect complex, carries the alternant as a free morph.
* With constituents ordered by containment, a host is the target itself, properly contains it,
  is properly contained in it, or is incomparable to it (`IncompRel (· ≤ ·)`, external hosting,
  as with the verb-hosted extraction morphology of the Mayan Agent Focus configuration). The
  predicates are stated in the order vocabulary over a reflex set and an explicit target, so a
  study asserts the target in the claim.
* `Reflex.Perceptible` is the claim that every designated target receives an overt reflex,
  which Tangale, Hausa and Yorùbá focus each refute.

## TODO

* The overlap-weakening of Hartmann and Zimmermann's Ex-Situ Generalisation for Hausa, which
  needs a structured-meaning overlap predicate.

## References

* [branan-erlewine-2023]
* [georgi-2017]
* [hartmann-zimmermann-2004]
* [hartmann-zimmermann-2007]
* [mccloskey-2002]
-/

@[expose] public section

/-- The channel of a reflex is the module whose output carries the trace, the literature's cut
between phonological, morphological and syntactic reflexes of one process. -/
inductive Reflex.Channel where
  | phonological | morphological | syntactic
  deriving DecidableEq, Repr

/-- A marking modality is a kind of perceptible perturbation. The two prosodic cases keep the
demarcative and the culminative apart. -/
inductive Reflex.Modality where
  /-- An exponent constituent surfaces displaced from its base position, a syntactic reflex. -/
  | displacement
  /-- A dedicated morpheme (affix, particle, or form alternation) at a host, a morphological
  reflex. -/
  | morpheme
  /-- A phrase edge at a host, a demarcative phonological reflex (the Tangale and Chadic
  pattern). -/
  | boundary
  /-- Metrical prominence on a host, a culminative phonological reflex (the English pattern). -/
  | prominence
  deriving DecidableEq, Repr

/-- A single overt reflex at a host constituent. -/
inductive Reflex (C : Type*) where
  /-- An exponent constituent surfaces displaced from its base position. -/
  | displacement (exponent : C)
  /-- A dedicated morpheme at a host constituent, coded by its marker. -/
  | morpheme (host : C) (marker : List Morphology.Morph)
  /-- A phrase edge at a host constituent. -/
  | boundary (edge : C)
  /-- Metrical prominence on a host constituent. -/
  | prominence (host : C)
  deriving DecidableEq, Repr

namespace Reflex

variable {C : Type*}

/-- The channel a modality marks in. -/
def Modality.channel : Modality → Channel
  | .displacement => .syntactic
  | .morpheme => .morphological
  | .boundary => .phonological
  | .prominence => .phonological

/-- The modality of a reflex. -/
def modality : Reflex C → Modality
  | .displacement _ => .displacement
  | .morpheme _ _ => .morpheme
  | .boundary _ => .boundary
  | .prominence _ => .prominence

/-- The host constituent of a reflex. -/
def host : Reflex C → C
  | .displacement c | .morpheme c _ | .boundary c | .prominence c => c

@[simp] theorem modality_displacement (c : C) : (displacement c).modality = .displacement := rfl
@[simp] theorem modality_morpheme (c : C) (m : List Morphology.Morph) :
    (morpheme c m).modality = .morpheme := rfl
@[simp] theorem modality_boundary (c : C) : (boundary c).modality = .boundary := rfl
@[simp] theorem modality_prominence (c : C) : (prominence c).modality = .prominence := rfl

@[simp] theorem host_displacement (c : C) : (displacement c).host = c := rfl
@[simp] theorem host_morpheme (c : C) (m : List Morphology.Morph) : (morpheme c m).host = c := rfl
@[simp] theorem host_boundary (c : C) : (boundary c).host = c := rfl
@[simp] theorem host_prominence (c : C) : (prominence c).host = c := rfl

/-- A morpheme reflex is coded by a nonempty marker; zero is never a reflex. -/
def IsOvert : Reflex C → Prop
  | .morpheme _ m => m ≠ []
  | _ => True

instance : ∀ ρ : Reflex C, Decidable ρ.IsOvert
  | .morpheme _ _ => inferInstanceAs (Decidable (_ ≠ _))
  | .displacement _ | .boundary _ | .prominence _ => inferInstanceAs (Decidable True)

/-- A marking system is perceptible when every designated target receives a reflex. -/
def Perceptible {ι : Type*} (realize : ι → Finset (Reflex C)) : Prop :=
  ∀ i, (realize i).Nonempty

/-! ### Host–target containment

With constituents ordered by containment, [branan-erlewine-2023] distinguish exact targeting,
pied-piping (a host properly contains the target) and anti-pied-piping (a host is properly
contained in the target, attested in over sixty languages). -/

section Containment

variable (s : Finset (Reflex C)) (target : C) {host : C}

/-- Every reflex is hosted by the designated constituent itself. -/
def ExactlyTargets : Prop := ∀ ρ ∈ s, ρ.host = target

instance [DecidableEq C] : Decidable (ExactlyTargets s target) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

variable {s target} in
theorem ExactlyTargets.exactlyTargets_iff (h : ExactlyTargets s host) (hs : s.Nonempty) :
    ExactlyTargets s target ↔ host = target :=
  ⟨fun h' ↦ hs.elim fun ρ hρ ↦ (h ρ hρ).symm.trans (h' ρ hρ), fun e ↦ e ▸ h⟩

variable [Preorder C]

/-- Some reflex is hosted by a constituent properly containing the target, which is Ross's
pied-piping as [branan-erlewine-2023] generalize it from movement to all marking morphosyntax. -/
def PiedPipes : Prop := ∃ ρ ∈ s, target < ρ.host

/-- Some reflex is hosted by a proper subconstituent of the target, which is
[branan-erlewine-2023]'s anti-pied-piping. -/
def AntiPiedPipes : Prop := ∃ ρ ∈ s, ρ.host < target

instance [DecidableLT C] : Decidable (PiedPipes s target) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance [DecidableLT C] : Decidable (AntiPiedPipes s target) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

variable {s target}

/-- A pied-piping reflex set does not exactly target its designee. -/
theorem PiedPipes.not_exactlyTargets (h : PiedPipes s target) : ¬ ExactlyTargets s target :=
  fun he ↦ let ⟨ρ, hρ, hlt⟩ := h; (he ρ hρ ▸ hlt).false

/-- An anti-pied-piping reflex set does not exactly target its designee. -/
theorem AntiPiedPipes.not_exactlyTargets (h : AntiPiedPipes s target) :
    ¬ ExactlyTargets s target :=
  fun he ↦ let ⟨ρ, hρ, hlt⟩ := h; (he ρ hρ ▸ hlt).false

/-- A nonempty reflex set hosted throughout by `host` pied-pipes a target exactly when `host`
properly contains it. -/
theorem ExactlyTargets.piedPipes_iff (h : ExactlyTargets s host) (hs : s.Nonempty) :
    PiedPipes s target ↔ target < host :=
  ⟨fun ⟨ρ, hρ, hlt⟩ ↦ h ρ hρ ▸ hlt, fun hlt ↦ hs.elim fun ρ hρ ↦ ⟨ρ, hρ, (h ρ hρ).symm ▸ hlt⟩⟩

/-- A nonempty reflex set hosted throughout by `host` anti-pied-pipes a target exactly when the
target properly contains `host`. -/
theorem ExactlyTargets.antiPiedPipes_iff (h : ExactlyTargets s host) (hs : s.Nonempty) :
    AntiPiedPipes s target ↔ host < target :=
  ⟨fun ⟨ρ, hρ, hlt⟩ ↦ h ρ hρ ▸ hlt, fun hlt ↦ hs.elim fun ρ hρ ↦ ⟨ρ, hρ, (h ρ hρ).symm ▸ hlt⟩⟩

end Containment

end Reflex
