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
    (hw : ∀ j ∈ I, w ∈ p j ↔ j = i) : w ∈ exhMW A (⋃ j ∈ I, p j) := by
  refine ⟨Set.mem_biUnion hi ((hw i hi).2 rfl), fun v hv hle ↦ ?_⟩
  obtain ⟨j, hj, hvj⟩ := Set.mem_iUnion₂.1 hv
  by_cases hji : j = i
  · subst hji
    refine fun q ⟨hq, hwq⟩ ↦ ⟨hq, ?_⟩
    obtain ⟨S, hS, rfl⟩ := hA q hq hwq
    obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.1 hwq
    exact Set.mem_biUnion hk (((hw k (hS hk)).1 hwk) ▸ hvj)
  · obtain ⟨S, hS, hSA, hjS, hiS⟩ := hsplit j hj hji
    obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.1 (hle ⟨hSA, Set.mem_biUnion hjS hvj⟩).2
    exact (hiS (((hw k (hS hk)).1 hwk) ▸ hk)).elim

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

end Exhaustification
