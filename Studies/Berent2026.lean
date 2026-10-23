module

public import Linglib.Fragments.English.Phonology
public import Linglib.Phonology.Segmental.Sonority
public import Linglib.Morphology.Root.Consonantal
public import Studies.BerentEtAl2016

/-!
# Berent (2026): Three arguments for abstraction in phonology

This file formalizes Berent's three experimental arguments that phonological grammar is
substance-free. Phonology is *abstract* (§3.1): onsets with large sonority rises are
preferred to small rises, these to plateaus, and these to falls, as in blif, bnif, bdif and
lbif, and the preference survives print presentation and the suppression of the lips or
the tongue. It is *algebraic* (§3.2): the Hebrew ban on roots that begin with two
identical consonants extends to /θ/, which Hebrew lacks, and the preference of ASL signers
for reduplication extends to unattested handshapes. It is *amodal* (§3.3): English
speakers project the doubling restrictions of their spoken language onto novel ASL signs.

Each property is stated as an invariance. The markedness of an onset is its sonority rise,
which depends on the two segments only through the major-class features that sonority
reads, so it is blind to the articulator that the suppression experiments manipulate.
Identity restrictions are invariant under any injective relabelling of the elements they
compare, so they cannot distinguish attested from unattested feature values. The doubling
reversal of `Studies/BerentEtAl2016.lean` holds over an arbitrary type of prosodic
constituents, spoken or signed.

## Main definitions

* `onsetRise`: the sonority rise across a two-consonant onset of feature-specified segments.
* `InitialIdentity`: a consonantal root begins with two identical consonants.

## Main results

* `sonority_cline`: the onsets of blif, bnif, bdif and lbif are a large rise, a small rise,
  a plateau and a fall.
* `onsetRise_congr`, `onsetRise_setFeature_left`: the rise is unchanged by any difference
  outside `Sonority.features`, and the labial onsets of plik, pnik and ptik pattern with
  those of blif, bnif and bdif.
* `initialIdentity_map`, `optimal_morphology_map`: the root restriction and the preference
  for reduplication give the same verdict on a form and on its image under an injective
  relabelling.
* `amodal_doubling_reversal`: the doubling reversal holds for any type of constituents and
  either ranking of the OCP and DEP.

## Implementation notes

The paper states the syllable hierarchy without a constraint set, deferring the formal
analysis to earlier work, so the hierarchy is the order on sonority rises and no tableau
is built. The acoustic, articulatory and neural measures of Figure 1 are not modelled.

## References

* [berent-2026]
* [berent-steriade-lennertz-vaknin-2007]
* [berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016]
* [mccarthy-1986]
-/

@[expose] public section

namespace Berent2026

open Phonology Morphology OptimalityTheory BerentEtAl2016

/-! ### Abstract: the syllable hierarchy -/

section Abstract

variable {c₁ c₂ d₁ d₂ : Segment}

/-- The sonority rise across a two-consonant onset. Larger rises are better formed. -/
def onsetRise (c₁ c₂ : Segment) : ℤ := Sonority.rise (.ofSegment c₁) (.ofSegment c₂)

/-- The rise of an onset depends on its segments only through the features that sonority
reads, whatever their place of articulation and laryngeal setting. -/
theorem onsetRise_congr (h₁ : ∀ f ∈ Sonority.features, c₁ f = d₁ f)
    (h₂ : ∀ f ∈ Sonority.features, c₂ f = d₂ f) : onsetRise c₁ c₂ = onsetRise d₁ d₂ := by
  rw [onsetRise, onsetRise, Sonority.ofSegment_congr h₁, Sonority.ofSegment_congr h₂]

/-- Changing a feature that sonority does not read in the first consonant leaves the rise
unchanged. -/
theorem onsetRise_setFeature_left {f : Feature} (hf : f ∉ Sonority.features) (v : Bool) :
    onsetRise (c₁.setFeature f v) c₂ = onsetRise c₁ c₂ := by
  rw [onsetRise, Sonority.ofSegment_setFeature hf, onsetRise]

theorem onsetRise_setFeature_right {f : Feature} (hf : f ∉ Sonority.features) (v : Bool) :
    onsetRise c₁ (c₂.setFeature f v) = onsetRise c₁ c₂ := by
  rw [onsetRise, Sonority.ofSegment_setFeature hf, onsetRise]

open English English.Phonology

/-- The onset of blif is a larger rise than that of bnif, the onset of bdif is a plateau,
and the onset of lbif is a fall. -/
theorem sonority_cline :
    0 < onsetRise b n ∧ onsetRise b n < onsetRise b l ∧ onsetRise b d = 0 ∧ onsetRise l b < 0 := by
  decide

theorem onsetRise_labial :
    onsetRise p l = onsetRise b l ∧ onsetRise p n = onsetRise b n ∧
      onsetRise p t = onsetRise b d :=
  ⟨onsetRise_congr (by decide) (by decide), onsetRise_congr (by decide) (by decide),
    onsetRise_congr (by decide) (by decide)⟩

end Abstract

/-! ### Algebraic: identity restrictions -/

section Algebraic

variable {α β : Type*} {f : α → β} {x y : α}

/-- A consonantal root begins with two identical consonants, the pattern that Hebrew bans
while allowing identical consonants at the end of a root. -/
def InitialIdentity (r : ConsonantalRoot α) : Prop := ¬ OCP.IsClean (r.segments.take 2)

instance [DecidableEq α] : DecidablePred (InitialIdentity (α := α)) :=
  fun _ ↦ inferInstanceAs (Decidable (¬ _))

theorem initialIdentity_double_left (x y : α) : InitialIdentity ⟨[x, x, y]⟩ := by
  simp [InitialIdentity]

theorem not_initialIdentity_double_right (h : y ≠ x) : ¬ InitialIdentity ⟨[y, x, x]⟩ := by
  simp [InitialIdentity, h]

/-- The root restriction gives the same verdict on a root and on its image under an
injective relabelling, so it extends to consonants the language lacks. -/
theorem initialIdentity_map (hf : Function.Injective f) (r : ConsonantalRoot α) :
    InitialIdentity ⟨r.segments.map f⟩ ↔ InitialIdentity r := by
  simp only [InitialIdentity, OCP.IsClean, ← List.map_take, List.isChain_map, hf.ne_iff]

theorem initialIdentity_theta :
    ¬ InitialIdentity (⟨[English.Phonology.k, English.Phonology.θ, English.Phonology.θ]⟩ :
        ConsonantalRoot Phonology.Segment) ∧
      InitialIdentity (⟨[English.Phonology.θ, English.Phonology.θ, English.Phonology.k]⟩ :
        ConsonantalRoot Phonology.Segment) :=
  ⟨not_initialIdentity_double_right (by decide +kernel), initialIdentity_double_left _ _⟩

/-- The preference for reduplication carries over to the image of the constituents under
an injective relabelling, so it extends to handshapes the language lacks. -/
theorem optimal_morphology_map [DecidableEq β] (hf : Function.Injective f) (h : x ≠ y)
    (r : Ranking (Fin 2) 2) :
    (tableau (f x) (f y) .morphology r).optimal = {.reduplicated [f x]} :=
  optimal_morphology (hf.ne h) r

end Algebraic

/-! ### Amodal: the doubling reversal -/

/-- The same identity ban yields opposite surface preferences at the two levels of
analysis. The constituents `x` and `y` range over any type, syllables of speech or of sign
alike, and the dependence on the spoken language is
`BerentEtAl2016.exists_optimal_surface_iff`. -/
theorem amodal_doubling_reversal {α : Type*} [DecidableEq α] {x y : α} (h : x ≠ y)
    (r : Ranking (Fin 2) 2) :
    (tableau x y .phonology r).optimal = {.simplex [x, y]} ∧
      (tableau x y .morphology r).optimal = {.reduplicated [x]} :=
  ⟨optimal_phonology h r, optimal_morphology h r⟩

end Berent2026
