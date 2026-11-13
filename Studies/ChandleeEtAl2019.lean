module

public import Studies.Hansson2010
public import Linglib.Data.Examples.ChandleeEtAl2019
public import Linglib.Phonology.Subregular.WordModel
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Minimal
public import Mathlib.Order.UpperLower.Closure

/-!
# Chandlee et al. (2019): Learning with Partially Ordered Representations

The paper orders the connected structures in models of strings by the subfactor relation and asks
a learner for the most general grammar of forbidden subfactors consistent with a sample. The
factors of a word form a lower set in that order, and the strictly local sets are the closed sets
of a closure operator, so [the minimal forbidden factors generate the closure of the
sample](##isAdequate_mostGeneral), uniquely so [up to equivalent
factors](##IsAdequate.image_toAntisymmetrization). For segments, [one feature-labelled subfactor
lies below the four sibilant pairs](##antPost_le_diagram) and [sorts the paper's Samala
words](##sibilantsOf_mem_language_iff); symmetric harmony needs [its mirror
image](##navajoSibilantHarmony_language_eq).

## Implementation notes

* Only the grammar that the algorithm of section 7 is to return is formalized, not the algorithm,
  nor the tree models of section 2.
* The Samala words are read for their sibilants, by the transcription reader of `Hansson2010`.
* The chart gives labials no [anterior] value, so t stands in for the paper's p, b, m.

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
  {i : ι} {D : Set ι} {G : Set (L.Factor k)}

variable (M) in
/-- The language of a grammar, Definition 8: the members none of whose `k`-factors the grammar
forbids. -/
def language (G : Set (L.Factor k)) : Set ι :=
  {i | Disjoint (L.factors k (M i)) G}

theorem mem_language_iff : i ∈ language M G ↔ ∀ g ∈ G, ¬ g.Occurs (M i) :=
  Set.disjoint_right

theorem isStrictlyLocal_language (G : Set (L.Factor k)) : L.IsStrictlyLocal M k (language M G) :=
  ⟨Gᶜ, Set.ext fun _ ↦ Set.subset_compl_iff_disjoint_right.symm⟩

-- Criteria 1 and 2 of Definition 9: the language covers the sample and lies in every strictly
-- local set that does.
theorem language_eq_strictlyLocalClosure_iff :
    language M G = L.strictlyLocalClosure M k D ↔
      D ⊆ language M G ∧ ∀ S, L.IsStrictlyLocal M k S → D ⊆ S → language M G ⊆ S := by
  set c := L.strictlyLocalClosure M k
  refine ⟨fun h ↦ ⟨h ▸ c.le_closure D, fun S hS hDS ↦ h ▸ c.closure_min hDS
    (isStrictlyLocal_iff_isClosed.1 hS)⟩, fun ⟨h₁, h₂⟩ ↦ le_antisymm ?_ ?_⟩
  · exact h₂ _ (isStrictlyLocal_iff_isClosed.2 (c.isClosed_closure D)) (c.le_closure D)
  · exact c.closure_min h₁ (isStrictlyLocal_iff_isClosed.1 (isStrictlyLocal_language G))

variable (L M k) in
/-- The forbidden factors of a sample, section 6: the factors of members that no datum
contains. -/
def forbidden (D : Set ι) : Set (L.Factor k) :=
  (⋃ i, L.factors k (M i)) \ ⋃ d ∈ D, L.factors k (M d)

theorem subset_forbidden (hG : G ⊆ ⋃ i, L.factors k (M i)) (hD : D ⊆ language M G) :
    G ⊆ forbidden L M k D := fun _ hg ↦ ⟨hG hg, fun h ↦
  let ⟨_, hd, hgd⟩ := Set.mem_iUnion₂.1 h
  Set.disjoint_left.1 (hD hd) hgd hg⟩

variable [L.IsRelational]

-- Proposition 3
theorem language_upperClosure (G : Set (L.Factor k)) :
    language M (upperClosure G : Set (L.Factor k)) = language M G :=
  Set.ext fun _ ↦ isLowerSet_factors.disjoint_upperClosure_right

variable (L M k) in
/-- The most general grammar of a sample: its minimal forbidden factors. -/
def mostGeneral (D : Set ι) : Set (L.Factor k) :=
  {g | Minimal (· ∈ forbidden L M k D) g}

variable (M) in
/-- A grammar of factors of members is adequate to a sample, Definition 9, when its language is the
sample's strictly local closure and its factors lie below those of every other such grammar. -/
structure IsAdequate (D : Set ι) (G : Set (L.Factor k)) : Prop where
  /-- The grammar consists of factors of members, as Definition 8 requires. -/
  subset_factors : G ⊆ ⋃ i, L.factors k (M i)
  /-- Criteria 1 and 2, by `language_eq_strictlyLocalClosure_iff`. -/
  language_eq : language M G = L.strictlyLocalClosure M k D
  /-- Criterion 3: each factor of another grammar meeting criteria 1 and 2 lies above one of
  this grammar's. -/
  exists_le : ∀ G' ⊆ ⋃ i, L.factors k (M i), language M G' = L.strictlyLocalClosure M k D →
    ∀ g' ∈ G', ∃ g ∈ G, g ≤ g'

theorem exists_mem_mostGeneral_le [WellFoundedLT (L.Factor k)] {f : L.Factor k}
    (hf : f ∈ forbidden L M k D) : ∃ g ∈ mostGeneral L M k D, g ≤ f :=
  let ⟨g, hgf, hg⟩ := exists_minimal_le_of_wellFoundedLT _ f hf
  ⟨g, hg, hgf⟩

theorem language_mostGeneral [WellFoundedLT (L.Factor k)] (D : Set ι) :
    language M (mostGeneral L M k D) = L.strictlyLocalClosure M k D := by
  ext i
  rw [mem_strictlyLocalClosure]
  refine ⟨fun hi f hf ↦ by_contra fun hfD ↦ ?_,
    fun h ↦ Set.disjoint_right.2 fun g hg hgi ↦ hg.prop.2 (h hgi)⟩
  obtain ⟨g, hg, hgf⟩ := exists_mem_mostGeneral_le ⟨Set.mem_iUnion.2 ⟨i, hf⟩, hfD⟩
  exact Set.disjoint_left.1 hi (isLowerSet_factors hgf hf) hg

/-- The minimal forbidden factors of a sample are adequate to it, which is what Theorem 1 asks of
the grammar the learning algorithm returns. -/
theorem isAdequate_mostGeneral [WellFoundedLT (L.Factor k)] (D : Set ι) :
    IsAdequate M D (mostGeneral L M k D) :=
  ⟨fun _ hg ↦ hg.prop.1, language_mostGeneral D, fun _ hG' h _ hg' ↦
    exists_mem_mostGeneral_le
      (subset_forbidden hG' (h ▸ (L.strictlyLocalClosure M k).le_closure D) hg')⟩

/-- Up to equivalent factors, an adequate grammar of pairwise incomparable factors is the most
general grammar. -/
theorem IsAdequate.image_toAntisymmetrization [WellFoundedLT (L.Factor k)]
    (hG : IsAdequate M D G) (hanti : IsAntichain (· ≤ ·) G) :
    toAntisymmetrization (· ≤ ·) '' G = toAntisymmetrization (· ≤ ·) '' mostGeneral L M k D := by
  have hF := subset_forbidden hG.subset_factors
    (hG.language_eq ▸ (L.strictlyLocalClosure M k).le_closure D)
  have hle (m) (hm : m ∈ mostGeneral L M k D) : ∃ g ∈ G, g ≤ m :=
    hG.exists_le _ (fun _ hg ↦ hg.prop.1) (language_mostGeneral D) m hm
  refine subset_antisymm (Set.image_mono fun g hg ↦ ⟨hF hg, fun f hf hfg ↦ ?_⟩) ?_
  · obtain ⟨m, hm, hmf⟩ := exists_mem_mostGeneral_le hf
    obtain ⟨g', hg', hg'm⟩ := hle m hm
    obtain rfl := hanti.eq hg' hg ((hg'm.trans hmf).trans hfg)
    exact hg'm.trans hmf
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨g, hg, hgm⟩ := hle m hm
    exact ⟨g, hg, (toAntisymmetrization_eq _ _ _).2 ⟨hgm, hm.2 (hF hg) hgm⟩⟩

end Grammar

/-! ### The examples of sections 4 and 6 -/

/-- The successor diagram of a two-letter word. -/
abbrev pair (a b : Char) : (wordLanguage Char).Factor 2 := succDiagram ({·}) [a, b] le_rfl

/-- The grammar of sections 4 and 6 forbids aa, bb and c. -/
def abGrammar : Set ((wordLanguage Char).Factor 2) :=
  {pair 'a' 'a', pair 'b' 'b', succDiagram ({·}) ['c'] (by simp)}

/-- The grammar of section 6 forbids the two-letter factors aa, bb and those with a c. -/
def twoLetterGrammar : Set ((wordLanguage Char).Factor 2) :=
  {pair 'a' 'a', pair 'b' 'b', pair 'a' 'c', pair 'b' 'c', pair 'c' 'c', pair 'c' 'a',
    pair 'c' 'b'}

theorem mem_language_abGrammar_twoLetterGrammar :
    ['a'] ∈ language (WordModel ({·}) · (· ⋖ ·)) abGrammar ∧
      ['c'] ∉ language (WordModel ({·}) · (· ⋖ ·)) abGrammar ∧
        ['c'] ∈ language (WordModel ({·}) · (· ⋖ ·)) twoLetterGrammar := by
  simp only [mem_language_iff, abGrammar, twoLetterGrammar, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, succDiagram_occurs_iff]
  decide

/-! ### Sibilants -/

/-- The signature of feature-labelled models of segment words. -/
abbrev featureLanguage : FirstOrder.Language := wordLanguage (Feature × Bool)

example (D : Set (List Segment)) :
    IsAdequate (WordModel featureValues · (· < ·)) D (mostGeneral featureLanguage (WordModel featureValues · (· < ·)) 2 D) :=
  isAdequate_mostGeneral D

/-- The class of the sibilants is [+strident]. -/
def strident : Segment := .ofSpecs [(.strident, true)]

/-- The alveolar sibilants are [+strident, +anterior]. -/
def alveolar : Segment := .ofSpecs [(.strident, true), (.anterior, true)]

/-- The postalveolar sibilants are [+strident, −anterior]. -/
def postalveolar : Segment := .ofSpecs [(.strident, true), (.anterior, false)]

/-- The forbidden subfactor of section 5.2 is an alveolar sibilant before a postalveolar one. -/
def antPost : featureLanguage.Factor 2 := diagram featureValues [alveolar, postalveolar] le_rfl

/-- The mirror image is a postalveolar sibilant before an alveolar one. -/
def postAnt : featureLanguage.Factor 2 := diagram featureValues [postalveolar, alveolar] le_rfl

theorem alveolar_le_iff (x : Segment) : alveolar ≤ x ↔ sibilantClass x = some true := by
  rw [alveolar, Segment.ofSpecs_le_iff_forall_mem x (by decide), sibilantClass]
  by_cases h : x.IsSibilant <;> simp_all [Segment.IsSibilant, Segment.HasValue]

theorem postalveolar_le_iff (x : Segment) : postalveolar ≤ x ↔ sibilantClass x = some false := by
  rw [postalveolar, Segment.ofSpecs_le_iff_forall_mem x (by decide), sibilantClass]
  by_cases h : x.IsSibilant <;> simp_all [Segment.IsSibilant, Segment.HasValue]

theorem diagram_pair_occurs_iff (d e : Segment) (w : List Segment) :
    (diagram featureValues [d, e] (k := 2) le_rfl).Occurs (WordModel featureValues w (· < ·)) ↔
      ∃ a b, [a, b] <+ w ∧ d ≤ a ∧ e ≤ b := by
  simp [diagram_occurs_iff_forall₂_le, List.forall₂_cons_left_iff]

theorem diagram_pair_le_iff (d e x y : Segment) :
    diagram featureValues [d, e] (k := 2) le_rfl ≤ diagram featureValues [x, y] le_rfl ↔
      d ≤ x ∧ e ≤ y := by
  rw [le_diagram_iff, diagram_pair_occurs_iff]
  refine ⟨fun ⟨a, b, hab, hd, he⟩ ↦ ?_, fun ⟨hd, he⟩ ↦ ⟨x, y, .refl _, hd, he⟩⟩
  obtain ⟨rfl, rfl⟩ : a = x ∧ b = y := by simpa using hab.eq_of_length rfl
  exact ⟨hd, he⟩

theorem mem_language_pair_iff {x y : Segment} {G : Set (featureLanguage.Factor 2)} :
    [x, y] ∈ language (WordModel featureValues · (· < ·)) G ↔ ∀ g ∈ G, ¬ g ≤ diagram featureValues [x, y] le_rfl := by
  simp only [mem_language_iff, le_diagram_iff]

/-- Each of the four sibilant pairs a conventional model forbids separately lies above the one
feature-labelled subfactor, which the grammar of section 5.2 forbids instead. -/
theorem antPost_le_diagram :
    ∀ x ∈ [s, z], ∀ y ∈ [esh, ezh], antPost ≤ diagram featureValues [x, y] le_rfl := by
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    antPost, diagram_pair_le_iff, alveolar_le_iff, postalveolar_le_iff]
  decide

/-- The alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- [+anterior] before [−anterior]. -/
def antNonant : featureLanguage.Factor 2 :=
  diagram featureValues [Segment.ofSpecs [(.anterior, true)], Segment.ofSpecs [(.anterior, false)]] le_rfl

/-- [+strident] before [+strident]. -/
def stridents : featureLanguage.Factor 2 := diagram featureValues [strident, strident] le_rfl

/-- The grammar of section 5.2 admits the sibilants of the Samala word the paper judges acceptable
and not those of the word it judges ungrammatical. -/
theorem sibilantsOf_mem_language_iff : ∀ e ∈ Examples.all,
    sibilantsOf e.primaryText.toList ∈ language (WordModel featureValues · (· < ·)) {antPost} ↔
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
    stridents ≤ diagram featureValues [s, s] le_rfl ∧ [s, s] ∈ language (WordModel featureValues · (· < ·)) {antPost} := by
  simp only [mem_language_pair_iff, Set.mem_singleton_iff, forall_eq, stridents, antPost,
    diagram_pair_le_iff, alveolar_le_iff, postalveolar_le_iff]
  decide

-- Forbidding [+ant][−ant] instead would exclude t…ʃ, which the grammar admits (section 5.2).
theorem t_esh_mem_language :
    antNonant ≤ diagram featureValues [t, esh] le_rfl ∧
      [t, esh] ∈ language (WordModel featureValues · (· < ·)) {antPost} := by
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
    navajoSibilantHarmony.language 2 = language (WordModel featureValues · (· < ·)) {antPost, postAnt} := by
  ext w
  rw [TierStrictlyLocalGrammar.mem_ofForbiddenPairs_language_iff_forall_sublist_pair
    (R := fun x y ↦ x .anterior ≠ y .anterior) (p := OnTier) fun _ _ _ _ _ _ ↦ by simp_all,
    mem_language_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, antPost,
    postAnt, diagram_pair_occurs_iff, alveolar_le_iff, postalveolar_le_iff, not_exists, not_and,
    ← forall_and]
  exact forall₂_congr fun a b ↦ imp_congr_right fun _ ↦ pair_agree_iff a b

theorem esh_s_mem_language :
    [esh, s] ∈ language (WordModel featureValues · (· < ·)) {antPost} ∧
      [esh, s] ∉ navajoSibilantHarmony.language 2 := by
  simp only [Set.ext_iff.1 navajoSibilantHarmony_language_eq [esh, s], mem_language_pair_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, antPost, postAnt,
    diagram_pair_le_iff, alveolar_le_iff, postalveolar_le_iff]
  decide

end ChandleeEtAl2019
