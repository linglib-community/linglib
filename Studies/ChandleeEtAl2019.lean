module

public import Studies.Hansson2010
public import Linglib.Phonology.Subregular.WordModel

/-!
# Chandlee et al. (2019): Learning with Partially Ordered Representations

The paper models strings by structures in which a position may carry several properties, so that
sounds share the values of their features, orders structures by the subfactor relation, and takes
a grammar to be a set of forbidden subfactors (Definition 8). Its phonological example
(section 5.2) bans an alveolar sibilant before a postalveolar one by a single forbidden subfactor
of the feature-labelled precedence model, [+str, +ant] before [+str, −ant], where a model with one
label per segment must ban sʃ, zʃ, sʒ and zʒ separately. Subfactors are factors in the sense of
`Core/ModelTheory/Factor.lean`, and the models of segment words are `Subregular.WordModel` with
the structure for the feature values, so a feature specification is a one-position subfactor
occurring where a segment of its natural class does, and a word's diagram occurs exactly in the
words with a subsequence above it. Hansson's symmetric Navajo harmony is the grammar of the
paper's subfactor and its mirror image (`mem_navajoSibilantHarmony_iff`), which the paper's
subfactor alone does not express (`esh_s_mem_language`).

## Implementation notes

The learning algorithm of sections 4 and 6 and its correctness are not formalized, nor are the
tree models of section 2.

## References

* [chandlee-eyraud-heinz-jardine-rawski-2019]
* [hansson-2010]
-/

@[expose] public section

namespace ChandleeEtAl2019

open FirstOrder.Language Subregular Subregular.WordModel Phonology Hansson2010 List
open Subregular.TierStrictlyLocalGrammar (mem_ofForbiddenPairs_language_iff_forall_sublist_pair)

/-- The signature of feature-labelled models of segment words. -/
abbrev featureLanguage : FirstOrder.Language := wordLanguage (Phonology.Feature × Bool)

/-! ### Natural classes as subfactors -/

/-- The class of the sibilants is [+strident]. -/
def strident : Segment := .ofSpecs [(.strident, true)]

/-- A one-position subfactor occurs exactly where a segment of its natural class does, so the
[+strident] subfactor occurs in the words with a sibilant. -/
theorem strident_occurs_iff (w : List Segment) :
    (diagram (Phonology.Feature × Bool) [strident] (k := 1) le_rfl).Occurs
      (WordModel w (· < ·)) ↔ ∃ x ∈ w, x.IsSibilant := by
  simp only [diagram_singleton_occurs_iff, labels_subset_labels_iff, strident,
    ← Segment.isSibilant_iff_le]

/-! ### The grammar of section 5.2 -/

/-- The alveolar sibilants are [+strident, +anterior]. -/
def alveolar : Segment := .ofSpecs [(.strident, true), (.anterior, true)]

/-- The postalveolar sibilants are [+strident, −anterior]. -/
def postalveolar : Segment := .ofSpecs [(.strident, true), (.anterior, false)]

/-- The forbidden subfactor of section 5.2 is an alveolar sibilant before a postalveolar one. -/
def antPost : featureLanguage.Factor 2 := diagram _ [alveolar, postalveolar] le_rfl

/-- The mirror image is a postalveolar sibilant before an alveolar one. -/
def postAnt : featureLanguage.Factor 2 := diagram _ [postalveolar, alveolar] le_rfl

/-- The language of the grammar, Definition 8, holds the words whose subfactors avoid the
forbidden one. -/
def language : Set (List Segment) :=
  {w | featureLanguage.factors 2 (WordModel w (· < ·)) ⊆ {antPost}ᶜ}

theorem language_isStrictlyLocal :
    featureLanguage.IsStrictlyLocal (fun w : List Segment ↦ WordModel w (· < ·)) 2 language :=
  ⟨_, rfl⟩

theorem mem_language_iff (w : List Segment) :
    w ∈ language ↔ ¬ antPost.Occurs (WordModel w (· < ·)) := by
  simp only [language, Set.mem_ofPred_eq, Set.subset_def, mem_factors, Set.mem_compl_iff,
    Set.mem_singleton_iff]
  exact ⟨fun h ho ↦ h _ ho rfl, fun h _ hx hxe ↦ h (hxe ▸ hx)⟩

/-- A two-position diagram occurs exactly where a subsequence of two segments lies above it. -/
theorem diagram_pair_occurs_iff (d e : Segment) (w : List Segment) :
    (diagram (Phonology.Feature × Bool) [d, e] (k := 2) le_rfl).Occurs (WordModel w (· < ·)) ↔
      ∃ a b, [a, b] <+ w ∧ d ≤ a ∧ e ≤ b := by
  rw [diagram_occurs_iff_forall₂_le]
  constructor
  · rintro ⟨t, htw, hdt⟩
    cases hdt with
    | cons hd hrest =>
      cases hrest with
      | cons he hnil =>
        cases hnil
        exact ⟨_, _, htw, hd, he⟩
  · rintro ⟨a, b, hab, hd, he⟩
    exact ⟨[a, b], hab, by simp [hd, he]⟩

theorem alveolar_le_iff (x : Segment) : alveolar ≤ x ↔ sibilantClass x = some true := by
  rw [alveolar, Segment.ofSpecs_le_iff_forall_mem x (by decide), sibilantClass]
  by_cases h : x.IsSibilant
  · simp_all [Segment.IsSibilant, Segment.HasValue]
  · simp_all [Segment.IsSibilant, Segment.HasValue]

theorem postalveolar_le_iff (x : Segment) : postalveolar ≤ x ↔ sibilantClass x = some false := by
  rw [postalveolar, Segment.ofSpecs_le_iff_forall_mem x (by decide), sibilantClass]
  by_cases h : x.IsSibilant
  · simp_all [Segment.IsSibilant, Segment.HasValue]
  · simp_all [Segment.IsSibilant, Segment.HasValue]

/-- One feature-labelled subfactor stands for the four segment factors sʃ, zʃ, sʒ and zʒ. -/
theorem antPost_occurs_sibilant_pairs :
    ∀ x ∈ [s, z], ∀ y ∈ [esh, ezh], antPost.Occurs (WordModel [x, y] (· < ·)) := by
  intro x hx y hy
  refine (diagram_pair_occurs_iff _ _ _).2 ⟨x, y, .refl _, ?_, ?_⟩
  · rw [alveolar_le_iff]; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> decide
  · rw [postalveolar_le_iff]; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl <;> decide

/-! ### Symmetric harmony -/

/-- Hansson's Navajo sibilant harmony is the language of the paper's forbidden subfactor
together with its mirror image. -/
theorem mem_navajoSibilantHarmony_iff (w : List Segment) :
    w ∈ navajoSibilantHarmony.language ↔
      ¬ antPost.Occurs (WordModel w (· < ·)) ∧ ¬ postAnt.Occurs (WordModel w (· < ·)) := by
  have htrans : ∀ a b c : Segment, OnTier a → OnTier b → OnTier c →
      ¬ a .anterior ≠ b .anterior → ¬ b .anterior ≠ c .anterior → ¬ a .anterior ≠ c .anterior :=
    fun _ _ _ _ _ _ hab hbc ↦ not_ne_iff.2 ((not_ne_iff.1 hab).trans (not_ne_iff.1 hbc))
  rw [mem_ofForbiddenPairs_language_iff_forall_sublist_pair htrans, antPost, postAnt,
    diagram_pair_occurs_iff, diagram_pair_occurs_iff]
  simp only [alveolar_le_iff, postalveolar_le_iff, not_exists, not_and, ne_eq, not_not]
  refine ⟨fun h ↦ ⟨fun a b hab ha hb ↦ ?_, fun a b hab ha hb ↦ ?_⟩, fun h a b hab hoa hob ↦ ?_⟩
  · have hoa : OnTier a := by simp [OnTier, ha]
    have hob : OnTier b := by simp [OnTier, hb]
    have := h a b hab hoa hob
    rw [← sibilantClass_of_onTier hoa, ← sibilantClass_of_onTier hob, ha, hb] at this
    cases this
  · have hoa : OnTier a := by simp [OnTier, ha]
    have hob : OnTier b := by simp [OnTier, hb]
    have := h a b hab hoa hob
    rw [← sibilantClass_of_onTier hoa, ← sibilantClass_of_onTier hob, ha, hb] at this
    cases this
  · rw [← sibilantClass_of_onTier hoa, ← sibilantClass_of_onTier hob]
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hoa
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hob
    rw [hu, hv]
    cases u <;> cases v
    · rfl
    · exact absurd hv (h.2 a b hab hu)
    · exact absurd hv (h.1 a b hab hu)
    · rfl

/-- The paper's subfactor alone admits a postalveolar sibilant before an alveolar one, which
Navajo's symmetric harmony bans. -/
theorem esh_s_mem_language : [esh, s] ∈ language ∧ [esh, s] ∉ navajoSibilantHarmony.language := by
  refine ⟨(mem_language_iff _).2 fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨a, b, hab, ha, -⟩ := (diagram_pair_occurs_iff _ _ _).1 h
    obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 (hab.eq_of_length rfl)
    exact absurd ((alveolar_le_iff _).1 ha) (by decide)
  · exact ((mem_navajoSibilantHarmony_iff _).1 h).2
      ((diagram_pair_occurs_iff _ _ _).2 ⟨esh, s, .refl _, by
        rw [postalveolar_le_iff]; decide, by rw [alveolar_le_iff]; decide⟩)

end ChandleeEtAl2019
