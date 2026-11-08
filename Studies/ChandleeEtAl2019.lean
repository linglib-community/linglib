module

public import Studies.Hansson2010
public import Linglib.Data.Examples.ChandleeEtAl2019
public import Linglib.Phonology.Subregular.WordModel
public import Mathlib.Order.Minimal
public import Mathlib.Order.UpperLower.Closure

/-!
# Chandlee et al. (2019): Learning with Partially Ordered Representations

The paper orders the connected structures in models of strings by the subfactor relation and asks
a learner for the most general grammar of forbidden subfactors consistent with a sample. The
factors of a word form a lower set under the subfactor preorder, so [a grammar forbids every
superfactor of what it forbids](##language_upperClosure), and [the minimal factors no datum
contains are the grammar the learner seeks](##isAdequate_mostGeneral). For segments, [one
feature-labelled subfactor lies below the four sibilant pairs](##antPost_le_diagram) a conventional
model forbids one by one, and [sorts the paper's Samala words](##sibilantsOf_mem_language_iff);
Hansson's symmetric harmony needs [its mirror image too](##navajoSibilantHarmony_language_eq).

## Implementation notes

* Only the grammar that the algorithm of section 7 is to return is formalized, not the algorithm,
  nor the tree models of section 2.
* The Samala words are read for their sibilants, by the transcription reader of `Hansson2010`.
* The chart gives labials no [anterior] value, so t stands in for the paper's p, b, m.

## Errata

* Section 4: the grammar forbidding aa, bb and c admits the word a, outside (ab)+ and (ba)+
  (`abGrammar_errata`).
* Section 6: that grammar and the grammar forbidding aa, bb, ac, bc, cc, ca and cb differ on the
  word c (`abGrammar_errata`).

## References

* [chandlee-eyraud-heinz-jardine-rawski-2019]
* [hansson-2010]
-/

@[expose] public section

namespace ChandleeEtAl2019

open Phonology Hansson2010 Subregular WordModel
open scoped List

/-! ### Grammars -/

section Grammar

open FirstOrder.Language

variable {L : FirstOrder.Language} {ι : Type*} {M : ι → Type*} [∀ i, L.Structure (M i)] {k : ℕ}
  {i : ι} {G : Set (L.Factor k)}

variable (M) in
/-- The language of a grammar, Definition 8: the members none of whose `k`-factors the grammar
forbids. -/
def language (G : Set (L.Factor k)) : Set ι :=
  {i | Disjoint (L.factors k (M i)) G}

theorem mem_language_iff : i ∈ language M G ↔ ∀ g ∈ G, ¬ g.Occurs (M i) :=
  Set.disjoint_right

theorem isStrictlyLocal_language (G : Set (L.Factor k)) : L.IsStrictlyLocal M k (language M G) :=
  ⟨Gᶜ, Set.ext fun _ ↦ Set.subset_compl_iff_disjoint_right.symm⟩

variable [L.IsRelational]

-- Proposition 3
theorem language_upperClosure (G : Set (L.Factor k)) :
    language M (upperClosure G : Set (L.Factor k)) = language M G :=
  Set.ext fun _ ↦ isLowerSet_factors.disjoint_upperClosure_right

variable (M) in
/-- A grammar of factors of members is adequate to a sample, Definition 9, when its language
covers the sample, is the least strictly local set that does, and its factors lie below those of
every other such grammar. -/
structure IsAdequate (D : Set ι) (G : Set (L.Factor k)) : Prop where
  /-- The grammar consists of factors of members, as Definition 8 requires. -/
  subset_factors : G ⊆ ⋃ i, L.factors k (M i)
  /-- Criterion 1: the language covers the sample. -/
  subset_language : D ⊆ language M G
  /-- Criterion 2: the language is the least strictly local set covering the sample. -/
  language_subset : ∀ S, L.IsStrictlyLocal M k S → D ⊆ S → language M G ⊆ S
  /-- Criterion 3: each factor of another grammar meeting criteria 1 and 2 lies above one of
  this grammar's. -/
  exists_le : ∀ G' ⊆ ⋃ i, L.factors k (M i), D ⊆ language M G' →
    (∀ S, L.IsStrictlyLocal M k S → D ⊆ S → language M G' ⊆ S) → ∀ g' ∈ G', ∃ g ∈ G, g ≤ g'

variable (L M k) in
/-- The minimal factors that occur in some member but in no datum. -/
def mostGeneral (D : Set ι) : Set (L.Factor k) :=
  {g | Minimal (· ∈ (⋃ i, L.factors k (M i)) \ ⋃ d ∈ D, L.factors k (M d)) g}

/-- The minimal factors that occur in some member but in no datum are adequate to the sample,
which is what Theorem 1 asks of the grammar the learning algorithm returns. -/
theorem isAdequate_mostGeneral [WellFoundedLT (L.Factor k)] (D : Set ι) :
    IsAdequate M D (mostGeneral L M k D) := by
  have key {f : L.Factor k} (hf : f ∈ (⋃ i, L.factors k (M i)) \ ⋃ d ∈ D, L.factors k (M d)) :
      ∃ g ∈ mostGeneral L M k D, g ≤ f :=
    let ⟨g, hgf, hg⟩ := exists_minimal_le_of_wellFoundedLT _ f hf
    ⟨g, hg, hgf⟩
  refine ⟨fun g hg ↦ hg.prop.1, fun d hd ↦ Set.disjoint_right.2 fun g hg hgd ↦
    hg.prop.2 (Set.mem_biUnion hd hgd), fun S hS hDS i hi ↦ ?_, fun G' hG' hD _ g' hg' ↦ ?_⟩
  · refine isStrictlyLocal_iff.1 hS i fun f hf ↦ by_contra fun hfS ↦ ?_
    obtain ⟨g, hg, hgf⟩ := key ⟨Set.mem_iUnion.2 ⟨i, hf⟩,
      fun h ↦ hfS (Set.biUnion_mono hDS (fun _ _ ↦ subset_rfl) h)⟩
    exact Set.disjoint_left.1 hi (isLowerSet_factors hgf hf) hg
  · refine key ⟨hG' hg', fun h ↦ ?_⟩
    obtain ⟨d, hd, hgd⟩ := Set.mem_iUnion₂.1 h
    exact Set.disjoint_left.1 (hD hd) hgd hg'

end Grammar

/-! ### The examples of sections 4 and 6 -/

/-- The successor diagram of a two-letter word. -/
abbrev pair (a b : Char) : (wordLanguage Char).Factor 2 := succDiagram Char [a, b] le_rfl

/-- The grammar of sections 4 and 6 forbids aa, bb and c. -/
def abGrammar : Set ((wordLanguage Char).Factor 2) :=
  {pair 'a' 'a', pair 'b' 'b', succDiagram Char ['c'] (by simp)}

/-- The grammar of section 6 forbids the two-letter factors aa, bb and those with a c. -/
def twoLetterGrammar : Set ((wordLanguage Char).Factor 2) :=
  {pair 'a' 'a', pair 'b' 'b', pair 'a' 'c', pair 'b' 'c', pair 'c' 'c', pair 'c' 'a',
    pair 'c' 'b'}

theorem abGrammar_errata :
    ['a'] ∈ language (WordModel · (· ⋖ ·)) abGrammar ∧
      ['c'] ∉ language (WordModel · (· ⋖ ·)) abGrammar ∧
        ['c'] ∈ language (WordModel · (· ⋖ ·)) twoLetterGrammar := by
  simp only [mem_language_iff, abGrammar, twoLetterGrammar, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, succDiagram_occurs_iff]
  decide

/-! ### Sibilants -/

/-- The signature of feature-labelled models of segment words. -/
abbrev featureLanguage : FirstOrder.Language := wordLanguage (Feature × Bool)

example (D : Set (List Segment)) :
    IsAdequate (WordModel · (· < ·)) D (mostGeneral featureLanguage (WordModel · (· < ·)) 2 D) :=
  isAdequate_mostGeneral D

/-- The class of the sibilants is [+strident]. -/
def strident : Segment := .ofSpecs [(.strident, true)]

/-- The alveolar sibilants are [+strident, +anterior]. -/
def alveolar : Segment := .ofSpecs [(.strident, true), (.anterior, true)]

/-- The postalveolar sibilants are [+strident, −anterior]. -/
def postalveolar : Segment := .ofSpecs [(.strident, true), (.anterior, false)]

/-- The forbidden subfactor of section 5.2 is an alveolar sibilant before a postalveolar one. -/
def antPost : featureLanguage.Factor 2 := diagram _ [alveolar, postalveolar] le_rfl

/-- The mirror image is a postalveolar sibilant before an alveolar one. -/
def postAnt : featureLanguage.Factor 2 := diagram _ [postalveolar, alveolar] le_rfl

theorem alveolar_le_iff (x : Segment) : alveolar ≤ x ↔ sibilantClass x = some true := by
  rw [alveolar, Segment.ofSpecs_le_iff_forall_mem x (by decide), sibilantClass]
  by_cases h : x.IsSibilant <;> simp_all [Segment.IsSibilant, Segment.HasValue]

theorem postalveolar_le_iff (x : Segment) : postalveolar ≤ x ↔ sibilantClass x = some false := by
  rw [postalveolar, Segment.ofSpecs_le_iff_forall_mem x (by decide), sibilantClass]
  by_cases h : x.IsSibilant <;> simp_all [Segment.IsSibilant, Segment.HasValue]

theorem diagram_pair_occurs_iff (d e : Segment) (w : List Segment) :
    (diagram (Feature × Bool) [d, e] (k := 2) le_rfl).Occurs (WordModel w (· < ·)) ↔
      ∃ a b, [a, b] <+ w ∧ d ≤ a ∧ e ≤ b := by
  simp [diagram_occurs_iff_forall₂_le, List.forall₂_cons_left_iff]

theorem diagram_pair_le_iff (d e x y : Segment) :
    diagram (Feature × Bool) [d, e] (k := 2) le_rfl ≤ diagram _ [x, y] le_rfl ↔
      d ≤ x ∧ e ≤ y := by
  rw [le_diagram_iff, diagram_pair_occurs_iff]
  refine ⟨fun ⟨a, b, hab, hd, he⟩ ↦ ?_, fun ⟨hd, he⟩ ↦ ⟨x, y, .refl _, hd, he⟩⟩
  obtain ⟨rfl, rfl⟩ : a = x ∧ b = y := by simpa using hab.eq_of_length rfl
  exact ⟨hd, he⟩

theorem mem_language_pair_iff {x y : Segment} {G : Set (featureLanguage.Factor 2)} :
    [x, y] ∈ language (WordModel · (· < ·)) G ↔ ∀ g ∈ G, ¬ g ≤ diagram _ [x, y] le_rfl :=
  mem_language_iff

/-- Each of the four sibilant pairs a conventional model forbids separately lies above the one
feature-labelled subfactor, which the grammar of section 5.2 forbids instead. -/
theorem antPost_le_diagram :
    ∀ x ∈ [s, z], ∀ y ∈ [esh, ezh], antPost ≤ diagram _ [x, y] le_rfl := by
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    antPost, diagram_pair_le_iff, alveolar_le_iff, postalveolar_le_iff]
  decide

/-- The alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- [+anterior] before [−anterior]. -/
def antNonant : featureLanguage.Factor 2 :=
  diagram _ [Segment.ofSpecs [(.anterior, true)], Segment.ofSpecs [(.anterior, false)]] le_rfl

/-- [+strident] before [+strident]. -/
def stridents : featureLanguage.Factor 2 := diagram _ [strident, strident] le_rfl

/-- The grammar of section 5.2 admits the sibilants of the Samala word the paper judges acceptable
and not those of the word it judges ungrammatical. -/
theorem sibilantsOf_mem_language_iff : ∀ e ∈ Examples.all,
    sibilantsOf e.primaryText.toList ∈ language (WordModel · (· < ·)) {antPost} ↔
      e.judgment = .acceptable := by
  simp only [Examples.all, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  rw [show sibilantsOf Examples.hasxintilawas.primaryText.toList = [s, s] by decide,
    show sibilantsOf Examples.hasxintilawaesh.primaryText.toList = [s, esh] by decide]
  simp only [mem_language_pair_iff, Set.mem_singleton_iff, forall_eq, antPost,
    diagram_pair_le_iff, alveolar_le_iff, postalveolar_le_iff]
  decide

-- Forbidding [+str][+str] instead would exclude s…s, which the grammar admits (section 5.2).
theorem s_s_mem_language :
    stridents ≤ diagram _ [s, s] le_rfl ∧ [s, s] ∈ language (WordModel · (· < ·)) {antPost} := by
  simp only [mem_language_pair_iff, Set.mem_singleton_iff, forall_eq, stridents, antPost,
    diagram_pair_le_iff, alveolar_le_iff, postalveolar_le_iff]
  decide

-- Forbidding [+ant][−ant] instead would exclude t…ʃ, which the grammar admits (section 5.2).
theorem t_esh_mem_language :
    antNonant ≤ diagram _ [t, esh] le_rfl ∧
      [t, esh] ∈ language (WordModel · (· < ·)) {antPost} := by
  simp only [mem_language_pair_iff, Set.mem_singleton_iff, forall_eq, antNonant, antPost,
    diagram_pair_le_iff, alveolar_le_iff, postalveolar_le_iff]
  decide

/-! ### Symmetric harmony -/

private theorem pair_agree_iff (a b : Segment) :
    (OnTier a → OnTier b → ¬ a .anterior ≠ b .anterior) ↔
      (sibilantClass a = some true → sibilantClass b ≠ some false) ∧
        (sibilantClass a = some false → sibilantClass b ≠ some true) := by
  rcases ha : sibilantClass a with _ | u
  · simp [OnTier, ha]
  rcases hb : sibilantClass b with _ | v
  · simp [OnTier, hb]
  have hoa : OnTier a := by simp [OnTier, ha]
  have hob : OnTier b := by simp [OnTier, hb]
  rw [← sibilantClass_of_onTier hoa, ← sibilantClass_of_onTier hob, ha, hb]
  cases u <;> cases v <;> simp [hoa, hob] <;> decide

/-- Hansson's symmetric sibilant harmony is the language of the grammar of the paper's subfactor
and its mirror image. -/
theorem navajoSibilantHarmony_language_eq :
    navajoSibilantHarmony.language 2 = language (WordModel · (· < ·)) {antPost, postAnt} := by
  ext w
  rw [TierStrictlyLocalGrammar.mem_ofForbiddenPairs_language_iff_forall_sublist_pair
    (R := fun x y ↦ x .anterior ≠ y .anterior) (p := OnTier) fun _ _ _ _ _ _ ↦ by simp_all,
    mem_language_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, antPost,
    postAnt, diagram_pair_occurs_iff, alveolar_le_iff, postalveolar_le_iff, not_exists, not_and,
    ← forall_and]
  exact forall₂_congr fun a b ↦ imp_congr_right fun _ ↦ pair_agree_iff a b

/-- The grammar of the paper's subfactor alone admits ʃ…s, which the symmetric harmony
forbids. -/
theorem esh_s_mem_language :
    [esh, s] ∈ language (WordModel · (· < ·)) {antPost} ∧
      [esh, s] ∉ navajoSibilantHarmony.language 2 := by
  simp only [Set.ext_iff.1 navajoSibilantHarmony_language_eq [esh, s], mem_language_pair_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, antPost, postAnt,
    diagram_pair_le_iff, alveolar_le_iff, postalveolar_le_iff]
  decide

end ChandleeEtAl2019
