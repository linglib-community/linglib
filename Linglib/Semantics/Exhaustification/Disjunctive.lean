module

public import Linglib.Semantics.Exhaustification.InnocentInclusion
public import Mathlib.Data.Finset.Card
public import Linglib.Core.Order.SupClosed

/-!
# Exhaustifying a disjunction against its closure under disjunction

A disjunction `⋃ i ∈ I, p i` whose alternatives lie in its closure under disjunction,
`supClosure (p '' I)`, the disjunctions over the nonempty subsets of `I` with no conjunctions,
strengthens under `exhIEII` to their conjunction, provided some world verifies each disjunct
alone and some world verifies all of them: nothing is innocently excludable, since a
single-disjunct world is minimal, and everything is innocently includable, since the cell is
consistent. With the whole closure the result is the conjunction of the disjuncts; with only the
disjunctions over subsets of size `m` it is that at least `|I| + 1 - m` disjuncts hold. This is
the generalization behind free choice without a conjunctive alternative and behind the
implicature account of homogeneity, where the disjuncts are the atoms of a plurality and pruning
to the size-`m` alternatives gives the non-maximal readings.

## References

* [bar-lev-2021]
* [bar-lev-fox-2020]
-/

@[expose] public section

namespace Exhaustification

variable {World ι : Type*} (I : Finset ι) (p : ι → Set World)

/-- `subDisjsOfCard I p m` collects the disjunction over `I` and the disjunctions over its
subsets of size `m`. -/
def subDisjsOfCard (m : ℕ) : Set (Set World) :=
  insert (⋃ i ∈ I, p i) {q | ∃ S ⊆ I, S.card = m ∧ q = ⋃ i ∈ S, p i}

variable {I p}

theorem subDisjsOfCard_subset_supClosure (hI : I.Nonempty) {m : ℕ} (hm : 0 < m) :
    subDisjsOfCard I p m ⊆ supClosure (p '' I) := by
  rintro q (rfl | ⟨S, hS, hcard, rfl⟩)
  · exact Set.mem_supClosure_image.2 ⟨I, hI, subset_rfl, rfl⟩
  · exact Set.mem_supClosure_image.2 ⟨S, Finset.card_pos.1 (hcard ▸ hm), hS, rfl⟩

section Family

variable {A : Set (Set World)}

theorem isMinimal_of_single {i : ι} (hi : i ∈ I) {w : World}
    (hA : ∀ q ∈ A, w ∈ q → ∃ S ⊆ I, q = ⋃ j ∈ S, p j)
    (hsplit : ∀ j ∈ I, j ≠ i → ∃ S ⊆ I, (⋃ k ∈ S, p k) ∈ A ∧ j ∈ S ∧ i ∉ S)
    (hw : ∀ j ∈ I, w ∈ p j ↔ j = i) : IsMinimal A (⋃ j ∈ I, p j) w := by
  refine ⟨Set.mem_biUnion hi ((hw i hi).2 rfl), ?_⟩
  rintro ⟨v, hv, hle, hnle⟩
  obtain ⟨j, hj, hvj⟩ := Set.mem_iUnion₂.1 hv
  by_cases hji : j = i
  · subst hji
    refine hnle fun q hq hwq ↦ ?_
    obtain ⟨S, hS, rfl⟩ := hA q hq hwq
    obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.1 hwq
    exact Set.mem_biUnion hk (((hw k (hS hk)).1 hwk) ▸ hvj)
  · obtain ⟨S, hS, hSA, hjS, hiS⟩ := hsplit j hj hji
    obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.1 (hle _ hSA (Set.mem_biUnion hjS hvj))
    exact hiS (((hw k (hS hk)).1 hwk) ▸ hk)

variable (hA : A ⊆ supClosure (p '' I))
  (hsplit : ∀ i ∈ I, ∀ j ∈ I, j ≠ i → ∃ S ⊆ I, (⋃ k ∈ S, p k) ∈ A ∧ j ∈ S ∧ i ∉ S)
  (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i)
include hA hsplit hsep

theorem not_isInnocentlyExcludable_of_subset_supClosure (q : Set World) :
    ¬ IsInnocentlyExcludable A (⋃ i ∈ I, p i) q := by
  intro hq
  obtain ⟨S, ⟨i, hi⟩, hS, rfl⟩ := Set.mem_supClosure_image.1 (hA hq.1)
  obtain ⟨w, hw⟩ := hsep i (hS hi)
  exact (isInnocentlyExcludable_iff_exhMW_subset_compl A _ _ hq.1).1 hq
    (isMinimal_of_single (hS hi) (fun q hq _ ↦
      let ⟨S, _, hS, h⟩ := Set.mem_supClosure_image.1 (hA hq); ⟨S, hS, h.symm⟩)
      (hsplit i (hS hi)) hw)
    (Set.mem_biUnion hi ((hw i (hS hi)).2 rfl))

theorem cell_nonempty_of_subset_supClosure (hI : I.Nonempty) (hall : ∃ w, ∀ i ∈ I, w ∈ p i) :
    (cell A (⋃ i ∈ I, p i)).Nonempty := by
  obtain ⟨w, hw⟩ := hall
  obtain ⟨i, hi⟩ := hI
  refine ⟨w, Set.mem_biUnion hi (hw i hi),
    fun q hq ↦ absurd hq (not_isInnocentlyExcludable_of_subset_supClosure hA hsplit hsep q),
    fun r ⟨hr, _⟩ ↦ ?_⟩
  obtain ⟨S, ⟨j, hj⟩, hS, rfl⟩ := Set.mem_supClosure_image.1 (hA hr)
  exact Set.mem_biUnion hj (hw j (hS hj))

theorem II_eq_self_of_subset_supClosure (hI : I.Nonempty) (hall : ∃ w, ∀ i ∈ I, w ∈ p i) :
    II A (⋃ i ∈ I, p i) = A := by
  rw [II_eq_nonExcludable_of_cell_nonempty _ _
    (cell_nonempty_of_subset_supClosure hA hsplit hsep hI hall)]
  ext q
  exact and_iff_left (not_isInnocentlyExcludable_of_subset_supClosure hA hsplit hsep q)

theorem exhIEII_eq_inter_sInter (hI : I.Nonempty) (hall : ∃ w, ∀ i ∈ I, w ∈ p i) :
    exhIEII A (⋃ i ∈ I, p i) = (⋃ i ∈ I, p i) ∩ ⋂₀ A := by
  rw [exhIEII_eq_cell_of_cell_nonempty _ _
    (cell_nonempty_of_subset_supClosure hA hsplit hsep hI hall)]
  ext w
  constructor
  · rintro ⟨hφ, _, hne⟩
    exact ⟨hφ, Set.mem_sInter.2 fun r hr ↦
      hne r ⟨hr, not_isInnocentlyExcludable_of_subset_supClosure hA hsplit hsep r⟩⟩
  · rintro ⟨hφ, hall'⟩
    exact ⟨hφ, fun q hq ↦
      absurd hq (not_isInnocentlyExcludable_of_subset_supClosure hA hsplit hsep q),
      fun r ⟨hr, _⟩ ↦ Set.mem_sInter.1 hall' r hr⟩

end Family

theorem hsplit_supClosure :
    ∀ i ∈ I, ∀ j ∈ I, j ≠ i → ∃ S ⊆ I, (⋃ k ∈ S, p k) ∈ supClosure (p '' I) ∧ j ∈ S ∧ i ∉ S :=
  fun _ _ j hj hji ↦ ⟨{j}, by simpa, Set.mem_supClosure_image.2 ⟨{j}, by simp, by simpa, rfl⟩,
    by simp, by simpa using hji.symm⟩

theorem exhIEII_supClosure (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i) (hI : I.Nonempty)
    (hall : ∃ w, ∀ i ∈ I, w ∈ p i) :
    exhIEII (supClosure (p '' I)) (⋃ i ∈ I, p i) = ⋂ i ∈ I, p i := by
  obtain ⟨i, hi⟩ := hI
  rw [exhIEII_eq_inter_sInter le_rfl hsplit_supClosure hsep ⟨i, hi⟩ hall, Set.sInter_supClosure,
    Set.sInter_image]
  simp only [Finset.mem_coe]
  exact Set.inter_eq_right.2 fun w hw ↦ Set.mem_biUnion hi (Set.mem_iInter₂.1 hw i hi)

theorem hsplit_subDisjsOfCard [DecidableEq ι] {m : ℕ} (hm : 0 < m) (hmI : m < I.card) :
    ∀ i ∈ I, ∀ j ∈ I, j ≠ i →
      ∃ S ⊆ I, (⋃ k ∈ S, p k) ∈ subDisjsOfCard I p m ∧ j ∈ S ∧ i ∉ S := by
  intro i hi j hj hji
  obtain ⟨S', hS', hcard⟩ := Finset.exists_subset_card_eq (s := (I.erase i).erase j) (n := m - 1)
    (by rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hji, hj⟩), Finset.card_erase_of_mem hi]
        omega)
  refine ⟨insert j S', ?_, Or.inr ⟨insert j S', ?_, ?_, rfl⟩, Finset.mem_insert_self _ _, ?_⟩
  · exact Finset.insert_subset hj
      ((hS'.trans (Finset.erase_subset _ _)).trans (Finset.erase_subset _ _))
  · exact Finset.insert_subset hj
      ((hS'.trans (Finset.erase_subset _ _)).trans (Finset.erase_subset _ _))
  · rw [Finset.card_insert_of_notMem (fun h ↦ (Finset.mem_erase.1 (hS' h)).1 rfl), hcard]; omega
  · intro h
    rcases Finset.mem_insert.1 h with rfl | h
    · exact hji rfl
    · exact (Finset.mem_erase.1 (Finset.mem_erase.1 (hS' h)).2).1 rfl

theorem forall_card_eq_exists_mem_iff [DecidableEq ι] {T : Finset ι} (hT : T ⊆ I) {m : ℕ} :
    (∀ S ⊆ I, S.card = m → ∃ i ∈ S, i ∈ T) ↔ I.card < m + T.card := by
  constructor
  · intro h
    by_contra hlt
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (s := I \ T) (n := m)
      (by rw [Finset.card_sdiff_of_subset hT]; omega)
    obtain ⟨i, hi, hiT⟩ := h S (hS.trans Finset.sdiff_subset) hcard
    exact (Finset.mem_sdiff.1 (hS hi)).2 hiT
  · intro h S hS hcard
    by_contra hnone
    push Not at hnone
    have : S ⊆ I \ T := fun i hi ↦ Finset.mem_sdiff.2 ⟨hS hi, hnone i hi⟩
    have h₁ := Finset.card_le_card this
    have h₂ := Finset.card_le_card hT
    rw [Finset.card_sdiff_of_subset hT, hcard] at h₁
    omega

theorem subDisjsOfCard_card : subDisjsOfCard I p I.card = {⋃ i ∈ I, p i} := by
  ext q
  simp only [subDisjsOfCard, Set.mem_insert_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    or_iff_left_iff_imp]
  rintro ⟨S, hS, hcard, rfl⟩
  rw [Finset.eq_of_subset_of_card_le hS hcard.ge]

theorem exhIEII_subDisjsOfCard [DecidableEq ι] [∀ w i, Decidable (w ∈ p i)]
    (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i) (hall : ∃ w, ∀ i ∈ I, w ∈ p i) {m : ℕ}
    (hm : 0 < m) (hmI : m ≤ I.card) :
    exhIEII (subDisjsOfCard I p m) (⋃ i ∈ I, p i) =
      {w | I.card < m + (I.filter fun i ↦ w ∈ p i).card} := by
  have hI : I.Nonempty := Finset.card_pos.1 (by omega)
  rcases hmI.lt_or_eq with hmI | rfl
  swap
  · have hsat : (⋃ i ∈ I, p i).Nonempty :=
      let ⟨w, hw⟩ := hall; let ⟨i, hi⟩ := hI; ⟨w, Set.mem_biUnion hi (hw i hi)⟩
    rw [subDisjsOfCard_card, exhIEII_singleton hsat]
    ext w
    constructor
    · intro h
      obtain ⟨i, hi, hw⟩ := Set.mem_iUnion₂.1 h
      have := Finset.card_pos.2
        (⟨i, Finset.mem_filter.2 ⟨hi, hw⟩⟩ : (I.filter fun i ↦ w ∈ p i).Nonempty)
      show I.card < I.card + _
      omega
    · intro h
      have h' : I.card < I.card + (I.filter fun i ↦ w ∈ p i).card := h
      have hpos : 0 < (I.filter fun i ↦ w ∈ p i).card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
      exact Set.mem_biUnion (Finset.mem_filter.1 hi).1 (Finset.mem_filter.1 hi).2
  rw [exhIEII_eq_inter_sInter (subDisjsOfCard_subset_supClosure hI hm)
    (hsplit_subDisjsOfCard hm hmI) hsep hI hall]
  ext w
  simp only [Set.mem_inter_iff, Set.mem_sInter, Set.mem_ofPred_eq]
  rw [← forall_card_eq_exists_mem_iff (Finset.filter_subset _ _)]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩ S hS hcard
    obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 (h _ (Or.inr ⟨S, hS, hcard, rfl⟩))
    exact ⟨i, hi, hS hi, hwi⟩
  · intro h
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (s := I) (n := m) hmI.le
    obtain ⟨i, hi, hiI, hwi⟩ := h S hS hcard
    refine ⟨Set.mem_biUnion hiI hwi, ?_⟩
    rintro r (rfl | ⟨S', hS', hcard', rfl⟩)
    · exact Set.mem_biUnion hiI hwi
    · obtain ⟨j, hj, _, hwj⟩ := h S' hS' hcard'
      exact Set.mem_biUnion hj hwj

theorem isInnocentlyExcludable_iInter_of_insert (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i)
    (h2 : 2 ≤ I.card) :
    IsInnocentlyExcludable (insert (⋂ i ∈ I, p i) (supClosure (p '' I))) (⋃ i ∈ I, p i)
      (⋂ i ∈ I, p i) := by
  refine (isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ (Set.mem_insert _ _)).2 ?_
  intro w ⟨hw, hmin⟩
  obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 hw
  obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (by omega : 1 < I.card) i
  intro hall
  simp only [Set.mem_iInter] at hall
  obtain ⟨v, hv⟩ := hsep i hi
  refine hmin ⟨v, Set.mem_biUnion hi ((hv i hi).2 rfl), ?_, fun hle ↦ ?_⟩
  · rintro q (rfl | hq) hvq
    · exact absurd (Set.mem_iInter₂.1 hvq j hj) (by rw [hv j hj]; exact hji)
    · obtain ⟨S, -, hS, rfl⟩ := Set.mem_supClosure_image.1 hq
      obtain ⟨k, hk, hvk⟩ := Set.mem_iUnion₂.1 hvq
      exact Set.mem_biUnion hk (((hv k (hS hk)).1 hvk) ▸ hwi)
  · exact hji ((hv j hj).1
      (hle _ (Or.inr (subset_supClosure (Set.mem_image_of_mem p hj))) (hall j hj)))

section Pair

variable {φ d₁ d₂ c : Set World} {w₁ w₂ : World}

theorem isMinimalCover_pair (hcov : φ ⊆ d₁ ∪ d₂) (h₁ : w₁ ∈ φ ∩ d₁ ∧ w₁ ∉ d₂ ∪ c)
    (h₂ : w₂ ∈ φ ∩ d₂ ∧ w₂ ∉ d₁ ∪ c) : IsMinimalCover {φ, d₁, d₂, c} φ {w₁, w₂} := by
  obtain ⟨⟨hw₁, hw₁₁⟩, hw₁'⟩ := h₁
  obtain ⟨⟨hw₂, hw₂₂⟩, hw₂'⟩ := h₂
  simp only [Set.mem_union, not_or] at hw₁' hw₂'
  refine ⟨by rintro v (rfl | rfl) <;> assumption, fun w hw ↦ ?_, ?_⟩
  · rcases hcov hw with h | h
    · refine ⟨w₁, by simp, fun q hq hq' ↦ ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl | rfl
      exacts [hw, h, absurd hq' hw₁'.1, absurd hq' hw₁'.2]
    · refine ⟨w₂, by simp, fun q hq hq' ↦ ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl | rfl
      exacts [hw, absurd hq' hw₂'.1, h, absurd hq' hw₂'.2]
  · intro v hv u hu huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hu
    rcases hv with rfl | rfl <;> rcases hu with rfl | rfl
    · exact leALT_refl _ _
    · exact absurd (huv d₂ (by simp) hw₂₂) hw₁'.1
    · exact absurd (huv d₁ (by simp) hw₁₁) hw₂'.1
    · exact leALT_refl _ _

theorem exhIEII_pair (hcov : φ ⊆ d₁ ∪ d₂) (h₁ : ∃ w ∈ φ ∩ d₁, w ∉ d₂ ∪ c)
    (h₂ : ∃ w ∈ φ ∩ d₂, w ∉ d₁ ∪ c) (h : ∃ w ∈ φ ∩ d₁ ∩ d₂, w ∉ c) :
    exhIEII {φ, d₁, d₂, c} φ = (φ ∩ d₁ ∩ d₂) \ c := by
  obtain ⟨w₁, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂⟩ := h₂
  obtain ⟨w₀, ⟨⟨hw₀, hw₀₁⟩, hw₀₂⟩, hw₀c⟩ := h
  have hM := isMinimalCover_pair hcov hw₁ hw₂
  obtain ⟨⟨hw₁, hw₁₁⟩, hw₁'⟩ := hw₁
  obtain ⟨⟨hw₂, hw₂₂⟩, hw₂'⟩ := hw₂
  simp only [Set.mem_union, not_or] at hw₁' hw₂'
  rw [hM.exhIEII_eq ⟨w₀, hw₀, ?_⟩]
  · ext w
    simp [hw₁, hw₂, hw₁₁, hw₂₂, hw₁'.1, hw₁'.2, hw₂'.1, hw₂'.2]
    tauto
  · simp [hw₁, hw₂, hw₁₁, hw₂₂, hw₁'.1, hw₁'.2, hw₂'.1, hw₂'.2, hw₀, hw₀₁, hw₀₂, hw₀c]

theorem exhIEII_pair_inter (hcov : φ ⊆ d₁ ∪ d₂) (h₁ : ∃ w ∈ φ ∩ d₁, w ∉ d₂)
    (h₂ : ∃ w ∈ φ ∩ d₂, w ∉ d₁) : exhIEII {φ, d₁, d₂, d₁ ∩ d₂} φ = φ \ (d₁ ∩ d₂) := by
  obtain ⟨w₁, ⟨hw₁, hw₁₁⟩, hw₁'⟩ := h₁
  obtain ⟨w₂, ⟨hw₂, hw₂₂⟩, hw₂'⟩ := h₂
  have hM := isMinimalCover_pair hcov (c := d₁ ∩ d₂)
    ⟨⟨hw₁, hw₁₁⟩, fun h ↦ hw₁' (h.elim id And.right)⟩
    ⟨⟨hw₂, hw₂₂⟩, fun h ↦ hw₂' (h.elim id And.left)⟩
  have hIE : ∀ q, IsInnocentlyExcludable {φ, d₁, d₂, d₁ ∩ d₂} φ q ↔ q = d₁ ∩ d₂ := by
    intro q
    constructor
    · intro hq
      have := (hM.isInnocentlyExcludable_iff hq.1).1 hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq] at this
      rcases hq.1 with rfl | rfl | rfl | rfl
      exacts [absurd hw₁ this.1, absurd hw₁₁ this.1, absurd hw₂₂ this.2, rfl]
    · rintro rfl
      exact (hM.isInnocentlyExcludable_iff (by simp)).2 (by simp [hw₁', hw₂'])
  have hMI : ∀ d ∈ ({d₁, d₂} : Set (Set World)), ∀ w ∈ φ ∩ d, w ∉ d₁ ∩ d₂ →
      Maximal (IsConsistentInclusion {φ, d₁, d₂, d₁ ∩ d₂} φ) {φ, d} := by
    intro d hd w ⟨hw, hwd⟩ hw'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    refine ⟨⟨?_, w, ⟨hw, fun q hq ↦ ((hIE q).1 hq) ▸ hw'⟩, ?_⟩,
      fun R' ⟨hR', u, hu, huR⟩ hRR' r hr ↦ ?_⟩
    · rcases hd with rfl | rfl <;> rintro r (rfl | rfl) <;> simp
    · rintro ψ (rfl | rfl)
      exacts [hw, hwd]
    · have hud : u ∈ d := huR d (hRR' (Or.inr rfl))
      have hu' : u ∉ d₁ ∩ d₂ := hu.2 _ ((hIE _).2 rfl)
      rcases hR' hr with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · rcases hd with rfl | rfl
        · exact Or.inr rfl
        · exact absurd ⟨huR r hr, hud⟩ hu'
      · rcases hd with rfl | rfl
        · exact absurd ⟨hud, huR r hr⟩ hu'
        · exact Or.inr rfl
      · exact absurd (huR _ hr) hu'
  ext w
  constructor
  · rintro ⟨hw, hIEw, -⟩
    exact ⟨hw, hIEw _ ((hIE _).2 rfl)⟩
  · rintro ⟨hw, hw'⟩
    refine ⟨hw, fun q hq ↦ ((hIE q).1 hq) ▸ hw', fun r hr ↦ ?_⟩
    have h₁ := hr.2 _ (hMI d₁ (by simp) w₁ ⟨hw₁, hw₁₁⟩ (fun h ↦ hw₁' h.2))
    have h₂ := hr.2 _ (hMI d₂ (by simp) w₂ ⟨hw₂, hw₂₂⟩ (fun h ↦ hw₂' h.1))
    rcases h₁ with rfl | rfl
    · exact hw
    · rcases h₂ with rfl | h
      · exact hw
      · exact absurd (h ▸ hw₁₁) hw₁'

theorem cell_pair_inter (hcov : φ ⊆ d₁ ∪ d₂) (h₁ : ∃ w ∈ φ ∩ d₁, w ∉ d₂)
    (h₂ : ∃ w ∈ φ ∩ d₂, w ∉ d₁) : cell {φ, d₁, d₂, d₁ ∩ d₂} φ = ∅ := by
  obtain ⟨w₁, ⟨hw₁, hw₁₁⟩, hw₁'⟩ := h₁
  obtain ⟨w₂, ⟨hw₂, hw₂₂⟩, hw₂'⟩ := h₂
  rw [(isMinimalCover_pair hcov (c := d₁ ∩ d₂) ⟨⟨hw₁, hw₁₁⟩, fun h ↦ hw₁' (h.elim id And.right)⟩
    ⟨⟨hw₂, hw₂₂⟩, fun h ↦ hw₂' (h.elim id And.left)⟩).cell_eq]
  ext w
  simp [hw₁, hw₂, hw₁₁, hw₂₂, hw₁', hw₂']
  tauto

theorem II_pair (hcov : φ ⊆ d₁ ∪ d₂) (h₁ : ∃ w ∈ φ ∩ d₁, w ∉ d₂ ∪ c)
    (h₂ : ∃ w ∈ φ ∩ d₂, w ∉ d₁ ∪ c) (h : ∃ w ∈ φ ∩ d₁ ∩ d₂, w ∉ c) :
    II {φ, d₁, d₂, c} φ = {φ, d₁, d₂} := by
  obtain ⟨w₁, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂⟩ := h₂
  obtain ⟨w₀, ⟨⟨hw₀, hw₀₁⟩, hw₀₂⟩, hw₀c⟩ := h
  have hM := isMinimalCover_pair hcov hw₁ hw₂
  obtain ⟨⟨hw₁, hw₁₁⟩, hw₁'⟩ := hw₁
  obtain ⟨⟨hw₂, hw₂₂⟩, hw₂'⟩ := hw₂
  simp only [Set.mem_union, not_or] at hw₁' hw₂'
  rw [hM.II_eq ⟨w₀, hw₀, by
    simp [hw₁, hw₂, hw₁₁, hw₂₂, hw₁'.1, hw₁'.2, hw₂'.1, hw₂'.2, hw₀, hw₀₁, hw₀₂, hw₀c]⟩]
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
    exists_eq_left]
  constructor
  · rintro ⟨rfl | rfl | rfl | rfl, h⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact absurd h (not_or.2 ⟨hw₁'.2, hw₂'.2⟩)
  · rintro (rfl | rfl | rfl) <;> simp [hw₁, hw₂, hw₁₁, hw₂₂]

theorem isInnocentlyExcludable_pair_iff (hcov : φ ⊆ d₁ ∪ d₂) (h₁ : ∃ w ∈ φ ∩ d₁, w ∉ d₂ ∪ c)
    (h₂ : ∃ w ∈ φ ∩ d₂, w ∉ d₁ ∪ c) {q : Set World} :
    IsInnocentlyExcludable {φ, d₁, d₂, c} φ q ↔ q = c := by
  obtain ⟨w₁, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂⟩ := h₂
  have hM := isMinimalCover_pair hcov hw₁ hw₂
  obtain ⟨⟨hw₁, hw₁₁⟩, hw₁'⟩ := hw₁
  obtain ⟨⟨hw₂, hw₂₂⟩, hw₂'⟩ := hw₂
  simp only [Set.mem_union, not_or] at hw₁' hw₂'
  refine ⟨fun hq ↦ ?_, ?_⟩
  · have := (hM.isInnocentlyExcludable_iff hq.1).1 hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq] at this
    rcases hq.1 with rfl | rfl | rfl | rfl
    exacts [absurd hw₁ this.1, absurd hw₁₁ this.1, absurd hw₂₂ this.2, rfl]
  · rintro rfl
    exact (hM.isInnocentlyExcludable_iff (by simp)).2 (by simp [hw₁'.2, hw₂'.2])

end Pair

section Cover

variable {φ : Set World} {x : ι → Set World}

theorem exhIEII_insert_range (hcov : φ ⊆ ⋃ i, x i)
    (hsep : ∀ i, ∃ w ∈ φ ∩ x i, ∀ j, j ≠ i → w ∉ x j) (h : ∃ w ∈ φ, ∀ i, w ∈ x i) :
    exhIEII (insert φ (Set.range x)) φ = φ ∩ ⋂ i, x i := by
  have hM : IsMinimalCover (insert φ (Set.range x)) φ
      {w | ∃ i, w ∈ φ ∩ x i ∧ ∀ j, j ≠ i → w ∉ x j} := by
    refine ⟨fun v ⟨i, hv, _⟩ ↦ hv.1, fun w hw ↦ ?_, ?_⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hw)
      obtain ⟨v, hv, hv'⟩ := hsep i
      refine ⟨v, ⟨i, hv, hv'⟩, ?_⟩
      rintro q (rfl | ⟨j, rfl⟩) hvq
      · exact hw
      · by_cases hji : j = i
        · exact hji ▸ hi
        · exact absurd hvq (hv' j hji)
    · rintro v ⟨i, hv, hv'⟩ u ⟨j, hu, hu'⟩ huv
      by_cases hji : j = i
      · subst hji
        rintro q (rfl | ⟨k, rfl⟩) hvq
        · exact hu.1
        · by_cases hkj : k = j
          · exact hkj ▸ hu.2
          · exact absurd hvq (hv' k hkj)
      · exact absurd (huv (x j) (Or.inr ⟨j, rfl⟩) hu.2) (hv' j hji)
  have hφ : ∀ w ∈ φ, ∃ v ∈ {w | ∃ i, w ∈ φ ∩ x i ∧ ∀ j, j ≠ i → w ∉ x j}, v ∈ φ := fun w hw ↦ by
    obtain ⟨i, -⟩ := Set.mem_iUnion.1 (hcov hw)
    obtain ⟨v, hv, hv'⟩ := hsep i
    exact ⟨v, ⟨i, hv, hv'⟩, hv.1⟩
  have hx : ∀ i, ∃ v ∈ {w | ∃ i, w ∈ φ ∩ x i ∧ ∀ j, j ≠ i → w ∉ x j}, v ∈ x i := fun i ↦ by
    obtain ⟨v, hv, hv'⟩ := hsep i
    exact ⟨v, ⟨i, hv, hv'⟩, hv.2⟩
  obtain ⟨w₀, hw₀, hw₀x⟩ := h
  rw [hM.exhIEII_eq ⟨w₀, hw₀, ?_⟩]
  · ext w
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hw, h⟩
      exact ⟨hw, fun i ↦ (h (x i) (Or.inr ⟨i, rfl⟩)).2 (hx i)⟩
    · rintro ⟨hw, h⟩
      refine ⟨hw, ?_⟩
      rintro q (rfl | ⟨i, rfl⟩)
      exacts [⟨fun _ ↦ hφ w hw, fun _ ↦ hw⟩, ⟨fun _ ↦ hx i, fun _ ↦ h i⟩]
  · rintro q (rfl | ⟨i, rfl⟩)
    exacts [⟨fun _ ↦ hφ w₀ hw₀, fun _ ↦ hw₀⟩, ⟨fun _ ↦ hx i, fun _ ↦ hw₀x i⟩]

end Cover

section Quantified

variable {φ s₁ s₂ sb e e₁ e₂ eb : Set World}

/-- Exhaustifying a disjunction under a quantifier yields universal free choice. The
alternatives replace the disjunction by its disjuncts and their conjunction and the quantifier by
a weaker one (`s` strong, `e` weak, `b` conjunctive). When each prejacent world verifies one of
three patterns (either disjunct's strong alternative with the weak alternatives, or the weak
alternatives alone), each pattern is realized exactly, and asserting both strong disjunct
alternatives while denying the conjunctive ones is consistent, exhaustification does exactly
that. -/
theorem exhIEII_quantified
    (hcov : ∀ w ∈ φ, (w ∈ s₁ ∧ w ∈ e ∧ w ∈ e₁) ∨ (w ∈ s₂ ∧ w ∈ e ∧ w ∈ e₂) ∨
      (w ∈ e ∧ w ∈ e₁ ∧ w ∈ e₂))
    (h₁ : ∃ w ∈ φ, w ∈ s₁ ∧ w ∈ e ∧ w ∈ e₁ ∧ w ∉ s₂ ∧ w ∉ sb ∧ w ∉ e₂ ∧ w ∉ eb)
    (h₂ : ∃ w ∈ φ, w ∈ s₂ ∧ w ∈ e ∧ w ∈ e₂ ∧ w ∉ s₁ ∧ w ∉ sb ∧ w ∉ e₁ ∧ w ∉ eb)
    (h₃ : ∃ w ∈ φ, w ∈ e ∧ w ∈ e₁ ∧ w ∈ e₂ ∧ w ∉ s₁ ∧ w ∉ s₂ ∧ w ∉ sb ∧ w ∉ eb)
    (h : ∃ w ∈ φ, w ∈ s₁ ∧ w ∈ s₂ ∧ w ∈ e ∧ w ∈ e₁ ∧ w ∈ e₂ ∧ w ∉ sb ∧ w ∉ eb) :
    exhIEII {φ, s₁, s₂, sb, e, e₁, e₂, eb} φ = (φ ∩ s₁ ∩ s₂ ∩ e ∩ e₁ ∩ e₂) \ (sb ∪ eb) := by
  obtain ⟨w₁, hw₁, hw₁s₁, hw₁e, hw₁e₁, hw₁s₂, hw₁sb, hw₁e₂, hw₁eb⟩ := h₁
  obtain ⟨w₂, hw₂, hw₂s₂, hw₂e, hw₂e₂, hw₂s₁, hw₂sb, hw₂e₁, hw₂eb⟩ := h₂
  obtain ⟨w₃, hw₃, hw₃e, hw₃e₁, hw₃e₂, hw₃s₁, hw₃s₂, hw₃sb, hw₃eb⟩ := h₃
  obtain ⟨w₀, hw₀, hw₀s₁, hw₀s₂, hw₀e, hw₀e₁, hw₀e₂, hw₀sb, hw₀eb⟩ := h
  have hM : IsMinimalCover {φ, s₁, s₂, sb, e, e₁, e₂, eb} φ {w₁, w₂, w₃} := by
    refine ⟨by rintro v (rfl | rfl | rfl) <;> assumption, fun w hw ↦ ?_, ?_⟩
    · rcases hcov w hw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · refine ⟨w₁, by simp, fun q hq hq' ↦ ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [hw, h1, absurd hq' hw₁s₂, absurd hq' hw₁sb, h2, h3, absurd hq' hw₁e₂,
          absurd hq' hw₁eb]
      · refine ⟨w₂, by simp, fun q hq hq' ↦ ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [hw, absurd hq' hw₂s₁, h1, absurd hq' hw₂sb, h2, absurd hq' hw₂e₁, h3,
          absurd hq' hw₂eb]
      · refine ⟨w₃, by simp, fun q hq hq' ↦ ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [hw, absurd hq' hw₃s₁, absurd hq' hw₃s₂, absurd hq' hw₃sb, h1, h2, h3,
          absurd hq' hw₃eb]
    · intro v hv u hu huv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hu
      rcases hv with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl
      · exact leALT_refl _ _
      · exact absurd (huv s₂ (by simp) hw₂s₂) hw₁s₂
      · exact absurd (huv e₂ (by simp) hw₃e₂) hw₁e₂
      · exact absurd (huv s₁ (by simp) hw₁s₁) hw₂s₁
      · exact leALT_refl _ _
      · exact absurd (huv e₁ (by simp) hw₃e₁) hw₂e₁
      · exact absurd (huv s₁ (by simp) hw₁s₁) hw₃s₁
      · exact absurd (huv s₂ (by simp) hw₂s₂) hw₃s₂
      · exact leALT_refl _ _
  rw [hM.exhIEII_eq ⟨w₀, hw₀, ?_⟩]
  · ext w
    simp [hw₁, hw₁s₁, hw₁e, hw₁e₁, hw₁s₂, hw₁sb, hw₁e₂, hw₁eb, hw₂, hw₂s₂, hw₂e, hw₂e₂, hw₂s₁,
      hw₂sb, hw₂e₁, hw₂eb, hw₃, hw₃e, hw₃e₁, hw₃e₂, hw₃s₁, hw₃s₂, hw₃sb, hw₃eb]
    tauto
  · simp [hw₁, hw₁s₁, hw₁e, hw₁e₁, hw₁s₂, hw₁sb, hw₁e₂, hw₁eb, hw₂, hw₂s₂, hw₂e, hw₂e₂, hw₂s₁,
      hw₂sb, hw₂e₁, hw₂eb, hw₃, hw₃e, hw₃e₁, hw₃e₂, hw₃s₁, hw₃s₂, hw₃sb, hw₃eb, hw₀, hw₀s₁, hw₀s₂,
      hw₀e, hw₀e₁, hw₀e₂, hw₀sb, hw₀eb]

end Quantified

end Exhaustification
