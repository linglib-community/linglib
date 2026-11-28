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
consistent. For any alternatives within the closure, having nothing innocently excludable is the
same as [being entailed by the conjunction of the disjuncts](##iInter_subset_exhIEII_iff), the
condition that pruning only weakens. With the whole closure the result is the conjunction of the
disjuncts; with only the
disjunctions over subsets of size `m` it is that at least `|I| + 1 - m` disjuncts hold. This is
the generalization behind free choice without a conjunctive alternative and behind the
implicature account of homogeneity, where the disjuncts are the atoms of a plurality and pruning
to the size-`m` alternatives gives the non-maximal readings.

Exhaustifying a sub-disjunction over the same closure affirms its disjuncts and denies the others
(`exhIEII_supClosure_biUnion`): its `minterm`, the cell of the partition the disjuncts induce
where exactly those disjuncts hold. The disjuncts form an independent family
(`IsIndependentFamily`) when every minterm is satisfiable. The conjunction of some members of a
family, exhaustified against the family, is their minterm as well (`exhIE_image_biInter`).

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

variable (I p) in
/-- The disjuncts are separated: each holds alone at some world, and all hold together at some
world. -/
structure Separating : Prop where
  /-- Each disjunct holds alone at some world. -/
  single : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i
  /-- All the disjuncts hold together at some world. -/
  all : ∃ w, ∀ i ∈ I, w ∈ p i

/-- Independent disjuncts, any nonempty combination of which is realized at some world, are
separated. -/
theorem Separating.of_forall_subset [DecidableEq ι]
    (h : ∀ T ⊆ I, T.Nonempty → ∃ w, ∀ i ∈ I, w ∈ p i ↔ i ∈ T) (hI : I.Nonempty) :
    Separating I p where
  single i hi :=
    let ⟨w, hw⟩ := h {i} (Finset.singleton_subset_iff.2 hi) (Finset.singleton_nonempty i)
    ⟨w, fun j hj ↦ (hw j hj).trans Finset.mem_singleton⟩
  all := let ⟨w, hw⟩ := h I subset_rfl hI; ⟨w, fun i hi ↦ (hw i hi).2 hi⟩

/-- For separated disjuncts, one disjunction entails another exactly when its disjuncts are
among the other's. -/
theorem biUnion_subset_biUnion_iff (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i)
    {S T : Finset ι} (hS : S ⊆ I) (hT : T ⊆ I) :
    ⋃ i ∈ S, p i ⊆ ⋃ i ∈ T, p i ↔ S ⊆ T := by
  refine ⟨fun h i hi ↦ ?_, fun h ↦ Set.biUnion_subset_biUnion_left (Finset.coe_subset.2 h)⟩
  obtain ⟨w, hw⟩ := hsep i (hS hi)
  obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.1 (h (Set.mem_biUnion hi ((hw i (hS hi)).2 rfl)))
  exact (hw k (hT hk)).1 hwk ▸ hk

/-- For separated disjuncts, taking the disjunction over a subset of them is an order
embedding. -/
def biUnionOrderEmbedding (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i) :
    {S : Finset ι // S ⊆ I} ↪o Set World :=
  OrderEmbedding.ofMapLEIff (fun S ↦ ⋃ i ∈ S.1, p i) fun S T ↦
    biUnion_subset_biUnion_iff hsep S.2 T.2

@[simp] theorem biUnionOrderEmbedding_apply (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i)
    (S : {S : Finset ι // S ⊆ I}) : biUnionOrderEmbedding hsep S = ⋃ i ∈ S.1, p i :=
  rfl

theorem Separating.biUnion_nonempty (h : Separating I p) (hI : I.Nonempty) :
    (⋃ i ∈ I, p i).Nonempty :=
  let ⟨w, hw⟩ := h.all
  let ⟨i, hi⟩ := hI
  ⟨w, Set.mem_biUnion hi (hw i hi)⟩

theorem biUnion_mem_supClosure (hI : I.Nonempty) : (⋃ i ∈ I, p i) ∈ supClosure (p '' I) :=
  Set.mem_supClosure_image.2 ⟨I, hI, subset_rfl, rfl⟩

theorem subset_biUnion_of_mem_supClosure {q : Set World} (hq : q ∈ supClosure (p '' I)) :
    q ⊆ ⋃ i ∈ I, p i := by
  obtain ⟨S, -, hS, rfl⟩ := Set.mem_supClosure_image.1 hq
  exact Set.biUnion_subset_biUnion_left hS

/-- Under negation every negated disjunction is entailed by the negated prejacent, so
exhaustification over any of them is vacuous. -/
theorem exhIEII_compl_biUnion {C : Set (Set World)} (hC : C ⊆ compl '' supClosure (p '' I))
    (hsat : (⋃ i ∈ I, p i)ᶜ.Nonempty) : exhIEII C (⋃ i ∈ I, p i)ᶜ = (⋃ i ∈ I, p i)ᶜ := by
  refine exhIEII_eq_self_of_forall_subset (fun q hq ↦ ?_) hsat
  obtain ⟨_, hq', rfl⟩ := hC hq
  exact Set.compl_subset_compl.2 (subset_biUnion_of_mem_supClosure hq')

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

theorem mem_of_mem_supClosure_image {w : World} (hw : ∀ i ∈ I, w ∈ p i) {q : Set World}
    (hq : q ∈ supClosure (p '' I)) : w ∈ q :=
  let ⟨_, ⟨j, hj⟩, hS, h⟩ := Set.mem_supClosure_image.1 hq
  h ▸ Set.mem_biUnion hj (hw j (hS hj))

section NoExclusion

variable (hA : A ⊆ supClosure (p '' I)) (hI : I.Nonempty) (hall : ∃ w, ∀ i ∈ I, w ∈ p i)
include hA hI hall

theorem cell_nonempty_of_forall_notMem_IE
    (hIE : ∀ q, ¬ q ∈ IE A (⋃ i ∈ I, p i)) : (cell A (⋃ i ∈ I, p i)).Nonempty :=
  let ⟨w, hw⟩ := hall
  let ⟨i, hi⟩ := hI
  ⟨w, Set.mem_biUnion hi (hw i hi), fun q hq ↦ absurd hq (hIE q),
    fun _ hr _ ↦ mem_of_mem_supClosure_image hw (hA hr)⟩

/-- When no alternative among the disjunctions is innocently excludable, exhaustification
asserts them all. -/
theorem exhIEII_eq_inter_sInter (hIE : ∀ q, ¬ q ∈ IE A (⋃ i ∈ I, p i)) :
    exhIEII A (⋃ i ∈ I, p i) = (⋃ i ∈ I, p i) ∩ ⋂₀ A := by
  rw [exhIEII_eq_cell_of_cell_nonempty _ _
    (cell_nonempty_of_forall_notMem_IE hA hI hall hIE)]
  ext w
  exact and_congr_right fun _ ↦ ⟨fun h ↦ Set.mem_sInter.2 fun r hr ↦ h.2 r hr (hIE r),
    fun h ↦ ⟨fun q hq ↦ absurd hq (hIE q), fun r hr _ ↦ Set.mem_sInter.1 h r hr⟩⟩

/-- Exhaustifying over some of the disjunctions is entailed by the conjunction of the disjuncts
exactly when none of them is innocently excludable. -/
theorem iInter_subset_exhIEII_iff :
    ⋂ i ∈ I, p i ⊆ exhIEII A (⋃ i ∈ I, p i) ↔
      ∀ q, ¬ q ∈ IE A (⋃ i ∈ I, p i) := by
  refine ⟨fun h q hq ↦ ?_, fun hIE ↦ ?_⟩
  · obtain ⟨w, hw⟩ := hall
    exact (h (Set.mem_iInter₂.2 hw)).2.1 q hq (mem_of_mem_supClosure_image hw (hA hq.1))
  · rw [exhIEII_eq_inter_sInter hA hI hall hIE]
    obtain ⟨i, hi⟩ := hI
    exact fun w hw ↦ ⟨Set.mem_biUnion hi (Set.mem_iInter₂.1 hw i hi), Set.mem_sInter.2 fun r hr ↦
      mem_of_mem_supClosure_image (fun i hi ↦ Set.mem_iInter₂.1 hw i hi) (hA hr)⟩

end NoExclusion

variable (hA : A ⊆ supClosure (p '' I))
  (hsplit : ∀ i ∈ I, ∀ j ∈ I, j ≠ i → ∃ S ⊆ I, (⋃ k ∈ S, p k) ∈ A ∧ j ∈ S ∧ i ∉ S)
  (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i)
include hA hsplit hsep

theorem notMem_IE_of_subset_supClosure (q : Set World) :
    ¬ q ∈ IE A (⋃ i ∈ I, p i) := by
  intro hq
  obtain ⟨S, ⟨i, hi⟩, hS, rfl⟩ := Set.mem_supClosure_image.1 (hA hq.1)
  obtain ⟨w, hw⟩ := hsep i (hS hi)
  exact (mem_IE_iff_exhMW_subset_compl A _ _ hq.1).1 hq
    (isMinimal_of_single (hS hi) (fun q hq _ ↦
      let ⟨S, _, hS, h⟩ := Set.mem_supClosure_image.1 (hA hq); ⟨S, hS, h.symm⟩)
      (hsplit i (hS hi)) hw)
    (Set.mem_biUnion hi ((hw i (hS hi)).2 rfl))

theorem cell_nonempty_of_subset_supClosure (hI : I.Nonempty) (hall : ∃ w, ∀ i ∈ I, w ∈ p i) :
    (cell A (⋃ i ∈ I, p i)).Nonempty :=
  cell_nonempty_of_forall_notMem_IE hA hI hall
    (notMem_IE_of_subset_supClosure hA hsplit hsep)

theorem mem_II_iff_of_subset_supClosure (hI : I.Nonempty)
    (hall : ∃ w, ∀ i ∈ I, w ∈ p i) {q : Set World} :
    q ∈ II A (⋃ i ∈ I, p i) ↔ q ∈ A := by
  rw [mem_II_iff_of_cell_nonempty
    (cell_nonempty_of_subset_supClosure hA hsplit hsep hI hall)]
  exact and_iff_left (notMem_IE_of_subset_supClosure hA hsplit hsep q)

end Family

/-- Two sets of sub-disjunctions that each make nothing innocently excludable make nothing
innocently excludable together. -/
theorem notMem_IE_union {A B : Set (Set World)}
    (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i) (hA : A ⊆ supClosure (p '' I))
    (hB : B ⊆ supClosure (p '' I)) (hIEA : ∀ q, ¬ q ∈ IE A (⋃ i ∈ I, p i))
    (hIEB : ∀ q, ¬ q ∈ IE B (⋃ i ∈ I, p i)) (q : Set World) :
    ¬ q ∈ IE (A ∪ B) (⋃ i ∈ I, p i) := by
  have key : ∀ {A B : Set (Set World)}, A ⊆ supClosure (p '' I) → B ⊆ supClosure (p '' I) →
      (∀ q, ¬ q ∈ IE A (⋃ i ∈ I, p i)) → q ∈ A →
      ¬ q ∈ IE (A ∪ B) (⋃ i ∈ I, p i) := by
    intro A B hA hB hIEA hqA hq
    have hfin : (A ∪ B).Finite :=
      (I.finite_toSet.image p).supClosure.subset (Set.union_subset hA hB)
    have hmw := (mem_IE_iff_exhMW_subset_compl (A ∪ B) _ q hq.1).1 hq
    have hnot := hIEA q
    rw [mem_IE_iff_exhMW_subset_compl A _ q hqA, Set.not_subset] at hnot
    obtain ⟨u₁, hu₁, hu₁q⟩ := hnot
    obtain ⟨S, -, hS, rfl⟩ := Set.mem_supClosure_image.1 (hA hqA)
    obtain ⟨i, hi, hu₁i⟩ := Set.mem_iUnion₂.1 (not_not.1 hu₁q)
    obtain ⟨w, hw⟩ := hsep i (hS hi)
    obtain ⟨u, hu, huw⟩ := exists_mem_exhMW_le hfin
      (Set.mem_biUnion (hS hi) ((hw i (hS hi)).2 rfl) : w ∈ ⋃ i ∈ I, p i)
    refine hmw hu (hu₁.2 hu.1 (fun r ⟨hr, hur⟩ ↦ ⟨hr, ?_⟩) ⟨hqA, not_not.1 hu₁q⟩).2
    obtain ⟨T, -, hT, rfl⟩ := Set.mem_supClosure_image.1 (hA hr)
    obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.1 (huw _ (Or.inl hr) hur)
    exact Set.mem_biUnion hk ((hw k (hT hk)).1 hwk ▸ hu₁i)
  intro hq
  rcases hq.1 with hqA | hqB
  · exact key hA hB hIEA hqA hq
  · exact key hB hA hIEB hqB (Set.union_comm A B ▸ hq)

theorem hsplit_supClosure :
    ∀ i ∈ I, ∀ j ∈ I, j ≠ i → ∃ S ⊆ I, (⋃ k ∈ S, p k) ∈ supClosure (p '' I) ∧ j ∈ S ∧ i ∉ S :=
  fun _ _ j hj hji ↦ ⟨{j}, by simpa, Set.mem_supClosure_image.2 ⟨{j}, by simp, by simpa, rfl⟩,
    by simp, by simpa using hji.symm⟩

/-! ### Minterms

The minterm of a set `T` of disjuncts holds where the disjuncts that hold are exactly those of
`T`. The minterms of the subsets of `I` are the cells of the partition the disjuncts induce, and
every Boolean combination of the disjuncts is a union of them. -/

section Minterm

variable {S T : Finset ι} {w : World}

variable (I p) in
/-- The worlds where the disjuncts of `I` that hold are exactly those of `T`. -/
def minterm (T : Finset ι) : Set World := {w | ∀ i ∈ I, w ∈ p i ↔ i ∈ T}

@[simp] theorem mem_minterm : w ∈ minterm I p T ↔ ∀ i ∈ I, w ∈ p i ↔ i ∈ T := Iff.rfl

theorem minterm_self : minterm I p I = ⋂ i ∈ I, p i := by
  ext w; simp +contextual

theorem minterm_empty : minterm I p ∅ = (⋃ i ∈ I, p i)ᶜ := by
  ext w; simp

/-- A world lies in the minterm of one subset of the disjuncts only. -/
theorem eq_of_mem_minterm (hS : S ⊆ I) (hT : T ⊆ I) (hwS : w ∈ minterm I p S)
    (hwT : w ∈ minterm I p T) : S = T :=
  Finset.Subset.antisymm (fun i hi ↦ (hwT i (hS hi)).1 ((hwS i (hS hi)).2 hi))
    fun i hi ↦ (hwS i (hT hi)).1 ((hwT i (hT hi)).2 hi)

theorem minterm_subset_biUnion (hT : T ⊆ I) (hne : T.Nonempty) :
    minterm I p T ⊆ ⋃ i ∈ I, p i :=
  fun _ hw ↦ let ⟨i, hi⟩ := hne; Set.mem_biUnion (hT hi) ((hw i (hT hi)).2 hi)

/-- A disjunction is the disjunction of the minterms of the nonempty sets of its disjuncts. -/
theorem biUnion_mem_supClosure_minterm (hI : I.Nonempty) :
    (⋃ i ∈ I, p i) ∈ supClosure (minterm I p '' {T | T ⊆ I ∧ T.Nonempty}) := by
  classical
  refine Set.mem_supClosure_image.2 ⟨I.powerset.erase ∅, ⟨I, by simp [hI.ne_empty]⟩,
    fun T hT ↦ by simpa [Finset.nonempty_iff_ne_empty, and_comm] using hT,
    Set.Subset.antisymm (Set.iUnion₂_subset fun T hT ↦ ?_) fun w hw ↦ ?_⟩
  · obtain ⟨hne, hTI⟩ := Finset.mem_erase.1 hT
    exact minterm_subset_biUnion (Finset.mem_powerset.1 hTI) (Finset.nonempty_iff_ne_empty.2 hne)
  · obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 hw
    exact Set.mem_biUnion (x := I.filter (w ∈ p ·)) (Finset.mem_erase.2
      ⟨Finset.ne_empty_of_mem (Finset.mem_filter.2 ⟨hi, hwi⟩),
        Finset.mem_powerset.2 (Finset.filter_subset _ _)⟩) fun j hj ↦ by simp [hj]

variable (I p) in
/-- The disjuncts form an independent family: every set of them is the set of those that hold at
some world. -/
def IsIndependentFamily : Prop := ∀ T ⊆ I, (minterm I p T).Nonempty

namespace IsIndependentFamily

variable (h : IsIndependentFamily I p)
include h

theorem separating (hI : I.Nonempty) : Separating I p := by
  classical exact .of_forall_subset (fun T hT _ ↦ h T hT) hI

theorem minterm_subset_minterm_iff (hS : S ⊆ I) (hT : T ⊆ I) :
    minterm I p S ⊆ minterm I p T ↔ S = T :=
  ⟨fun hsub ↦ let ⟨_, hw⟩ := h S hS; eq_of_mem_minterm hS hT hw (hsub hw), fun h ↦ h ▸ subset_rfl⟩

theorem minterm_subset_biUnion_iff (hT : T ⊆ I) :
    minterm I p T ⊆ ⋃ i ∈ I, p i ↔ T.Nonempty := by
  refine ⟨fun hsub ↦ ?_, minterm_subset_biUnion hT⟩
  obtain ⟨w, hw⟩ := h T hT
  obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 (hsub hw)
  exact ⟨i, (hw i hi).1 hwi⟩

theorem not_minterm_subset_compl_minterm (hT : T ⊆ I) :
    ¬ minterm I p T ⊆ (minterm I p T)ᶜ :=
  fun hsub ↦ let ⟨_, hw⟩ := h T hT; hsub hw hw

end IsIndependentFamily

/-- Exhaustified against the family, the conjunction of the members of `T` holds where exactly
they do, its minterm, when some world is in it. -/
theorem exh_image_biInter (hT : T ⊆ I) (h : (minterm I p T).Nonempty) :
    exh (p '' I) (⋂ i ∈ T, p i) = minterm I p T := by
  obtain ⟨v, hv⟩ := h
  ext w
  rw [mem_exh_image_iff, mem_minterm, Set.mem_iInter₂]
  refine ⟨fun ⟨hw, hex⟩ i hi ↦ ⟨fun hwi ↦ (hv i hi).1 (hex i hi hwi
      (Set.mem_iInter₂.2 fun j hj ↦ (hv j (hT hj)).2 hj)), hw i⟩,
    fun hw ↦ ⟨fun i hi ↦ (hw i (hT hi)).2 hi,
      fun i hi hwi _ hu ↦ Set.mem_iInter₂.1 hu i ((hw i hi).1 hwi)⟩⟩

/-- Innocent exclusion gives the minterm too, since plain exhaustification is consistent. -/
theorem exhIE_image_biInter (hT : T ⊆ I) (h : (minterm I p T).Nonempty) :
    exhIE (p '' I) (⋂ i ∈ T, p i) = minterm I p T := by
  have he := exh_image_biInter hT h
  rw [exhIE_eq_exh_of_nonempty _ _ (he ▸ h), he]

theorem IsIndependentFamily.exhIE_image_biInter (h : IsIndependentFamily I p) (hT : T ⊆ I) :
    exhIE (p '' I) (⋂ i ∈ T, p i) = minterm I p T :=
  Exhaustification.exhIE_image_biInter hT (h T hT)

end Minterm

/-- A disjunction is innocently excludable against a sub-disjunction of separated disjuncts
exactly when the two share no disjunct. -/
theorem mem_IE_supClosure_biUnion_iff {T : Finset ι} (hTI : T ⊆ I)
    (hsingle : ∀ i ∈ T, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i) {S : Finset ι} (hS : S ⊆ I)
    (hSne : S.Nonempty) :
    (⋃ i ∈ S, p i) ∈ IE (supClosure (p '' I)) (⋃ i ∈ T, p i) ↔ Disjoint S T := by
  have hmem (R : Finset ι) (hR : R ⊆ I) (hne : R.Nonempty) : ⋃ i ∈ R, p i ∈ supClosure (p '' I) :=
    Set.mem_supClosure_image.2 ⟨R, hne, hR, rfl⟩
  rw [mem_IE_iff_exhMW_subset_compl _ _ _ (hmem S hS hSne), Finset.disjoint_left]
  refine ⟨fun h i hiS hiT ↦ ?_, fun h u hu huq ↦ ?_⟩
  · obtain ⟨w, hw⟩ := hsingle i hiT
    refine h ⟨Set.mem_biUnion hiT ((hw i (hTI hiT)).2 rfl), fun v hv hle q ⟨hq, hwq⟩ ↦ ⟨hq, ?_⟩⟩
      (Set.mem_biUnion hiS ((hw i (hTI hiT)).2 rfl))
    obtain ⟨k, hk, hvk⟩ := Set.mem_iUnion₂.1 hv
    have hki : k = i := (hw k (hTI hk)).1 <| by
      simpa using (hle ⟨hmem {k} (by simpa using hTI hk) (by simp), by simpa using hvk⟩).2
    obtain ⟨R, -, hR, rfl⟩ := Set.mem_supClosure_image.1 hq
    obtain ⟨j, hj, hwj⟩ := Set.mem_iUnion₂.1 hwq
    exact Set.mem_biUnion hj ((hw j (hR hj)).1 hwj ▸ hki ▸ hvk)
  · obtain ⟨j, hj, huj⟩ := Set.mem_iUnion₂.1 huq
    obtain ⟨i, hi, hui⟩ := Set.mem_iUnion₂.1 hu.1
    obtain ⟨w, hw⟩ := hsingle i hi
    have hle := hu.2 (Set.mem_biUnion hi ((hw i (hTI hi)).2 rfl) : w ∈ ⋃ i ∈ T, p i)
      fun q ⟨hq, hwq⟩ ↦ ⟨hq, by
        obtain ⟨R, -, hR, rfl⟩ := Set.mem_supClosure_image.1 hq
        obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.1 hwq
        exact Set.mem_biUnion hk ((hw k (hR hk)).1 hwk ▸ hui)⟩
    have : w ∈ p j := by
      simpa using (hle ⟨hmem {j} (by simpa using hS hj) (by simp), by simpa using huj⟩).2
    exact h hj ((hw j (hS hj)).1 this ▸ hi)

/-- Exhaustifying a sub-disjunction over the closure of all the disjuncts under disjunction
affirms its disjuncts and denies the others. -/
theorem exhIEII_supClosure_biUnion {T : Finset ι} (hTI : T ⊆ I) (hne : T.Nonempty)
    (hsingle : ∀ i ∈ T, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i) (hT : (minterm I p T).Nonempty) :
    exhIEII (supClosure (p '' I)) (⋃ i ∈ T, p i) = minterm I p T := by
  have hcell : cell (supClosure (p '' I)) (⋃ i ∈ T, p i) = minterm I p T := by
    ext w
    refine ⟨fun ⟨_, hIE, hII⟩ i hi ↦ ⟨fun hwi ↦ ?_, fun hiT ↦ ?_⟩, fun hw ↦ ⟨?_, ?_, ?_⟩⟩
    · by_contra hiT
      refine hIE _ ((mem_IE_supClosure_biUnion_iff hTI hsingle (S := {i})
        (by simpa using hi) (by simp)).2 (by simpa using hiT)) (by simpa using hwi)
    · have := hII (⋃ j ∈ ({i} : Finset ι), p j)
        (Set.mem_supClosure_image.2 ⟨{i}, by simp, by simpa using hi, rfl⟩) fun h ↦ by
          have := (mem_IE_supClosure_biUnion_iff hTI hsingle (S := {i})
            (by simpa using hi) (by simp)).1 h
          simp_all
      simpa using this
    · obtain ⟨i, hi⟩ := hne
      exact Set.mem_biUnion hi ((hw i (hTI hi)).2 hi)
    · intro q hq hwq
      obtain ⟨S, hSne, hS, rfl⟩ := Set.mem_supClosure_image.1 hq.1
      obtain ⟨j, hj, hwj⟩ := Set.mem_iUnion₂.1 hwq
      exact Finset.disjoint_left.1
        ((mem_IE_supClosure_biUnion_iff hTI hsingle hS hSne).1 hq) hj
        ((hw j (hS hj)).1 hwj)
    · intro r hr hnr
      obtain ⟨S, hSne, hS, rfl⟩ := Set.mem_supClosure_image.1 hr
      rw [mem_IE_supClosure_biUnion_iff hTI hsingle hS hSne,
        Finset.not_disjoint_iff] at hnr
      obtain ⟨j, hjS, hjT⟩ := hnr
      exact Set.mem_biUnion hjS ((hw j (hS hjS)).2 hjT)
  rw [exhIEII_eq_cell_of_cell_nonempty _ _ (hcell ▸ hT), hcell]

/-- In an independent family, exhaustifying a sub-disjunction over the closure of all the disjuncts
under disjunction gives its minterm. -/
theorem IsIndependentFamily.exhIEII_supClosure_biUnion (h : IsIndependentFamily I p)
    {T : Finset ι} (hTI : T ⊆ I) (hne : T.Nonempty) :
    exhIEII (supClosure (p '' I)) (⋃ i ∈ T, p i) = minterm I p T :=
  Exhaustification.exhIEII_supClosure_biUnion hTI hne
    (fun i hi ↦ (h {i} (by simpa using hTI hi)).imp fun _ hw j hj ↦ (hw j hj).trans (by simp))
    (h T hTI)

/-- Exhaustifying a disjunction of separated disjuncts over its closure under disjunction gives
their conjunction. -/
theorem exhIEII_supClosure (h : Separating I p) (hI : I.Nonempty) :
    exhIEII (supClosure (p '' I)) (⋃ i ∈ I, p i) = ⋂ i ∈ I, p i := by
  obtain ⟨w, hw⟩ := h.all
  rw [exhIEII_supClosure_biUnion subset_rfl hI h.single ⟨w, fun i hi ↦ iff_of_true (hw i hi) hi⟩,
    minterm_self]

theorem hsplit_image :
    ∀ i ∈ I, ∀ j ∈ I, j ≠ i → ∃ S ⊆ I, (⋃ k ∈ S, p k) ∈ p '' ↑I ∧ j ∈ S ∧ i ∉ S :=
  fun _ _ j hj hji ↦ ⟨{j}, by simpa, ⟨j, hj, by simp⟩, by simp, by simpa using hji.symm⟩

/-- Against its disjuncts alone, a disjunction of separated disjuncts has nothing innocently
excludable. -/
theorem exhIE_image (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i) :
    exhIE (p '' ↑I) (⋃ i ∈ I, p i) = ⋃ i ∈ I, p i :=
  Set.Subset.antisymm (exhIE_subset _ _) fun _ hw ↦ ⟨hw, fun q hq ↦ absurd hq
    (notMem_IE_of_subset_supClosure subset_supClosure hsplit_image hsep q)⟩

/-- Exhaustifying a disjunction of separated disjuncts against the disjuncts alone gives their
conjunction. -/
theorem exhIEII_image (h : Separating I p) (hI : I.Nonempty) :
    exhIEII (p '' ↑I) (⋃ i ∈ I, p i) = ⋂ i ∈ I, p i := by
  obtain ⟨i, hi⟩ := hI
  rw [exhIEII_eq_inter_sInter subset_supClosure ⟨i, hi⟩ h.all
      (notMem_IE_of_subset_supClosure subset_supClosure hsplit_image h.single),
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

section Count

variable [∀ w i, Decidable (w ∈ p i)]

variable (I p) in
/-- The number of disjuncts true at `w`. -/
def trueCount (w : World) : ℕ := (I.filter fun i ↦ w ∈ p i).card

variable (I p) in
/-- At least `k` of the disjuncts are true. -/
def atLeastTrue (k : ℕ) : Set World := {w | k ≤ trueCount I p w}

@[simp] theorem mem_atLeastTrue {k : ℕ} {w : World} :
    w ∈ atLeastTrue I p k ↔ k ≤ trueCount I p w := Iff.rfl

theorem trueCount_le_card (w : World) : trueCount I p w ≤ I.card := Finset.card_filter_le _ _

theorem trueCount_pos {w : World} : 0 < trueCount I p w ↔ w ∈ ⋃ i ∈ I, p i := by
  simp [trueCount, Finset.card_pos, Finset.filter_nonempty_iff]

theorem trueCount_eq_card {w : World} : trueCount I p w = I.card ↔ w ∈ ⋂ i ∈ I, p i := by
  simp [trueCount, Finset.card_filter_eq_iff]

theorem atLeastTrue_antitone : Antitone (atLeastTrue I p) := fun _ _ hkl _ hw ↦ hkl.trans hw

theorem atLeastTrue_one : atLeastTrue I p 1 = ⋃ i ∈ I, p i :=
  Set.ext fun _ ↦ trueCount_pos

theorem atLeastTrue_card : atLeastTrue I p I.card = ⋂ i ∈ I, p i :=
  Set.ext fun w ↦ ⟨fun h ↦ trueCount_eq_card.1 (le_antisymm (trueCount_le_card w) h),
    fun h ↦ (trueCount_eq_card.2 h).ge⟩

/-- Exhaustifying over the disjunctions of `m` disjuncts gives "at least `|I| + 1 - m` of them
hold". -/
theorem exhIEII_subDisjsOfCard [DecidableEq ι] (h : Separating I p) {m : ℕ} (hm : 0 < m)
    (hmI : m ≤ I.card) :
    exhIEII (subDisjsOfCard I p m) (⋃ i ∈ I, p i) = atLeastTrue I p (I.card + 1 - m) := by
  obtain ⟨hsep, hall⟩ := h
  suffices key : exhIEII (subDisjsOfCard I p m) (⋃ i ∈ I, p i) =
      {w | I.card < m + (I.filter fun i ↦ w ∈ p i).card} by
    rw [key]
    ext w
    change I.card < m + trueCount I p w ↔ I.card + 1 - m ≤ trueCount I p w
    omega
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
  rw [exhIEII_eq_inter_sInter (subDisjsOfCard_subset_supClosure hI hm) hI hall
    (notMem_IE_of_subset_supClosure (subDisjsOfCard_subset_supClosure hI hm)
      (hsplit_subDisjsOfCard hm hmI) hsep)]
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

end Count

/-- Once the conjunction of the disjuncts joins their closure under disjunction, it is innocently
excludable. -/
theorem mem_IE_iInter_of_insert (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i)
    (h2 : 2 ≤ I.card) :
    (⋂ i ∈ I, p i) ∈ IE (insert (⋂ i ∈ I, p i) (supClosure (p '' I))) (⋃ i ∈ I, p i) := by
  refine (mem_IE_iff_exhMW_subset_compl _ _ _ (Set.mem_insert _ _)).2 ?_
  intro w ⟨hw, hmin⟩
  obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 hw
  obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (by omega : 1 < I.card) i
  intro hall
  simp only [Set.mem_iInter] at hall
  obtain ⟨v, hv⟩ := hsep i hi
  have hle := hmin (Set.mem_biUnion hi ((hv i hi).2 rfl)) fun q ⟨hq, hvq⟩ ↦ ⟨hq, ?_⟩
  · exact hji ((hv j hj).1
      (hle ⟨Or.inr (subset_supClosure (Set.mem_image_of_mem p hj)), hall j hj⟩).2)
  rcases hq with rfl | hq
  · exact absurd (Set.mem_iInter₂.1 hvq j hj) (by rw [hv j hj]; exact hji)
  · obtain ⟨S, -, hS, rfl⟩ := Set.mem_supClosure_image.1 hq
    obtain ⟨k, hk, hvk⟩ := Set.mem_iUnion₂.1 hvq
    exact Set.mem_biUnion hk (((hv k (hS hk)).1 hvk) ▸ hwi)

end Exhaustification
