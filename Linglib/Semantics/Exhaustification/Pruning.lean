module

public import Linglib.Semantics.Exhaustification.Disjunctive
public import Linglib.Semantics.Questions.Partition.Basic

/-!
# Pruning the alternatives of a disjunction

A disjunction exhaustified over its closure under disjunction means the conjunction of its
disjuncts. Pruning replaces that set of alternatives by a subset, and it is constrained to weaken:
the result over the subset must be entailed by the result over the whole set. For separated
disjuncts that holds [exactly when the subset makes nothing innocently
excludable](##mem_prunedReadings_iff), so every derived reading is a conjunction of
sub-disjunctions, and when the disjuncts are independent the derived readings are [exactly those
conjunctions that are not themselves proper sub-disjunctions](##prunedReadings_eq). "At least `k`
of the disjuncts hold" [is among them](##atLeastTrue_mem_prunedReadings) for every `k`. A question
selects the strongest derived reading it determines, and [every derived reading is selected by the
polar question whether it holds](##isPrunedReading_polar).

## Implementation notes

`IsPrunedReading` states the outcome of minimal pruning, the strongest derived reading the
question determines; the requirement that the pruned set be a maximal one with a relevant result
is not stated separately.

## References

* [bar-lev-2021]
* [crnic-chemla-fox-2015]
-/

@[expose] public section

namespace Exhaustification

variable {World ι : Type*} {I : Finset ι} {p : ι → Set World}

/-! ### The readings pruning derives -/

variable (I p) in
/-- The readings of the disjunction that pruning derives: the results of exhaustifying over a
set of its sub-disjunctions that only weakens the result of exhaustifying over all of them. -/
def prunedReadings : Set (Set World) :=
  (exhIEII · (⋃ i ∈ I, p i)) '' {C | C ⊆ supClosure (p '' I) ∧
    exhIEII (supClosure (p '' I)) (⋃ i ∈ I, p i) ⊆
      exhIEII C (⋃ i ∈ I, p i)}

/-- A pruning only weakens exactly when it leaves nothing innocently excludable, and then
exhaustification asserts every alternative it keeps. -/
theorem mem_prunedReadings_iff (h : Separating I p) (hne : I.Nonempty) {r : Set World} :
    r ∈ prunedReadings I p ↔ ∃ C ⊆ supClosure (p '' I),
      (∀ q, ¬ IsInnocentlyExcludable C (⋃ i ∈ I, p i) q) ∧
        (⋃ i ∈ I, p i) ∩ ⋂₀ C = r := by
  simp only [prunedReadings, Set.mem_image, Set.mem_ofPred_eq,
    exhIEII_supClosure h hne, and_assoc]
  refine exists_congr fun C ↦ and_congr_right fun hC ↦ ?_
  rw [iInter_subset_exhIEII_iff hC hne h.all]
  exact and_congr_right fun hIE ↦ by rw [exhIEII_eq_inter_sInter hC hne h.all hIE]

theorem subset_biUnion_of_mem_prunedReadings {r : Set World} (hr : r ∈ prunedReadings I p) :
    r ⊆ ⋃ i ∈ I, p i := by
  obtain ⟨C, -, rfl⟩ := hr
  exact fun _ hw ↦ hw.1

theorem iInter_subset_of_mem_prunedReadings (h : Separating I p) (hne : I.Nonempty)
    {r : Set World} (hr : r ∈ prunedReadings I p) : ⋂ i ∈ I, p i ⊆ r := by
  obtain ⟨C, ⟨-, hC⟩, rfl⟩ := hr
  rwa [exhIEII_supClosure h hne] at hC

theorem biUnion_mem_prunedReadings (h : Separating I p) (hne : I.Nonempty) :
    (⋃ i ∈ I, p i) ∈ prunedReadings I p :=
  ⟨{⋃ i ∈ I, p i}, ⟨Set.singleton_subset_iff.2 (biUnion_mem_supClosure hne),
    (exhIEII_singleton (h.biUnion_nonempty hne)).symm ▸ fun _ hw ↦ hw.1⟩,
    exhIEII_singleton (h.biUnion_nonempty hne)⟩

theorem iInter_mem_prunedReadings (h : Separating I p) (hne : I.Nonempty) :
    ⋂ i ∈ I, p i ∈ prunedReadings I p :=
  ⟨_, ⟨subset_rfl, subset_rfl⟩, exhIEII_supClosure h hne⟩

private theorem inter_sInter_mem_infClosure {S C : Set (Set World)} {φ : Set World} (hφ : φ ∈ S)
    (hfin : C.Finite) (hC : C ⊆ S) : φ ∩ ⋂₀ C ∈ infClosure S := by
  induction C, hfin using Set.Finite.induction_on with
  | empty => simpa using subset_infClosure hφ
  | @insert a C _ _ ih =>
    rw [Set.sInter_insert, Set.inter_left_comm]
    exact infClosed_infClosure (subset_infClosure (hC (Set.mem_insert _ _)))
      (ih ((Set.subset_insert _ _).trans hC))

theorem prunedReadings_subset_infClosure (h : Separating I p) (hne : I.Nonempty) :
    prunedReadings I p ⊆ infClosure (supClosure (p '' I)) := by
  intro r hr
  obtain ⟨C, hC, -, rfl⟩ := (mem_prunedReadings_iff h hne).1 hr
  exact inter_sInter_mem_infClosure (biUnion_mem_supClosure hne)
    ((I.finite_toSet.image _).supClosure.subset hC) hC

/-- A conjunction of sub-disjunctions that is not itself a proper sub-disjunction is derived by
keeping every sub-disjunction it entails. -/
theorem infClosure_diff_subset_prunedReadings (h : Separating I p) (hne : I.Nonempty) :
    infClosure (supClosure (p '' I)) \
      (supClosure (p '' I) \ {⋃ i ∈ I, p i}) ⊆ prunedReadings I p := by
  rintro r ⟨⟨t, ht, hts, hrt⟩, hr⟩
  have hrC : (⋃ i ∈ I, p i) ∩ ⋂₀ {q ∈ supClosure (p '' I) | r ⊆ q} = r := by
    refine Set.Subset.antisymm (fun w hw ↦ ?_)
      (Set.subset_inter ?_ (Set.subset_sInter fun _ hq ↦ hq.2))
    · rw [← hrt, Finset.inf'_eq_inf, Finset.inf_set_eq_iInter]
      exact Set.mem_iInter₂.2 fun q hq ↦ Set.mem_sInter.1 hw.2 q
        ⟨hts hq, hrt ▸ Finset.inf'_le id hq⟩
    · obtain ⟨q, hq⟩ := ht
      exact (hrt ▸ Finset.inf'_le id hq).trans (subset_biUnion_of_mem_supClosure (hts hq))
  refine (mem_prunedReadings_iff h hne).2 ⟨_, fun _ hq ↦ hq.1, fun q hIE ↦ ?_, hrC⟩
  have hfin := (I.finite_toSet.image (p)).supClosure.subset
    (fun _ hq ↦ hq.1 : {q ∈ supClosure (p '' I) | r ⊆ q} ⊆ _)
  have hmw := (isInnocentlyExcludable_iff_exhMW_subset_compl _ _ q hIE.1).1 hIE
  obtain ⟨hqS, hrq⟩ := hIE.1
  obtain ⟨s, -, hsx, rfl⟩ := Set.mem_supClosure_image.1 hqS
  have hmin : ∀ q' ∈ {q ∈ supClosure (p '' I) | r ⊆ q},
      ⋃ i ∈ s, p i ⊆ q' := by
    intro q' hq'
    obtain ⟨s', -, hs'x, rfl⟩ := Set.mem_supClosure_image.1 hq'.1
    refine Set.biUnion_subset_biUnion_left (s := (s : Set ι)) (s' := (s' : Set ι)) fun i hi ↦
      by_contra fun hi' ↦ ?_
    obtain ⟨wi, hwi⟩ := h.single i (hsx hi)
    obtain ⟨u, hu, hle⟩ := exists_mem_exhMW_le hfin
      (Set.mem_biUnion (hsx hi) ((hwi i (hsx hi)).2 rfl))
    obtain ⟨j, hj, huj⟩ := Set.mem_iUnion₂.1 hu.1
    rcases (hle ⟨⟨supClosed_supClosure hq'.1 (subset_supClosure (Set.mem_image_of_mem _ hj)),
      hq'.2.trans Set.subset_union_left⟩, Or.inr huj⟩).2 with hw | hw
    · obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.1 hw
      exact hi' ((hwi k (hs'x hk)).1 hwk ▸ hk)
    · exact hmw hu (Set.mem_biUnion hi ((hwi j hj).1 hw ▸ huj))
  have hrs : r = ⋃ i ∈ s, p i :=
    hrC ▸ Set.Subset.antisymm (Set.inter_subset_right.trans (Set.sInter_subset_of_mem ⟨hqS, hrq⟩))
      (Set.subset_inter (subset_biUnion_of_mem_supClosure hqS) (Set.subset_sInter hmin))
  have hrφ : r = ⋃ i ∈ I, p i := by_contra fun hne' ↦ hr ⟨hrs ▸ hqS, hne'⟩
  obtain ⟨u, hu⟩ := exhMW_nonempty hfin (h.biUnion_nonempty hne)
  exact hmw hu (by rw [← hrs, hrφ]; exact hu.1)

/-- When the disjuncts are independent, no proper sub-disjunction is a reading. -/
theorem eq_biUnion_of_mem_prunedReadings_of_mem_supClosure [DecidableEq ι]
    (hind : ∀ T ⊆ I, ∃ w, ∀ i ∈ I, w ∈ p i ↔ i ∈ T) (hne : I.Nonempty) {r : Set World}
    (hr : r ∈ prunedReadings I p) (hrS : r ∈ supClosure (p '' I)) :
    r = ⋃ i ∈ I, p i := by
  obtain ⟨C, hC, hIE, rfl⟩ := (mem_prunedReadings_iff (.of_forall_subset hind) hne).1 hr
  obtain ⟨s, -, hsx, hs⟩ := Set.mem_supClosure_image.1 hrS
  by_contra hneq
  obtain ⟨j, hj, hjs⟩ : ∃ j ∈ I, j ∉ s := by
    by_contra hcon
    push Not at hcon
    exact hneq (Set.Subset.antisymm Set.inter_subset_left
      (hs ▸ Set.biUnion_subset_biUnion_left (s := (I : Set ι))
        (s' := (s : Set ι)) fun j hj ↦ hcon j hj))
  obtain ⟨v, hv⟩ := hind (I.filter (· ∉ s)) (Finset.filter_subset _ _)
  have hvφ : v ∈ ⋃ i ∈ I, p i :=
    Set.mem_biUnion hj ((hv j hj).2 (Finset.mem_filter.2 ⟨hj, hjs⟩))
  have hvs : v ∉ ⋃ i ∈ s, p i := fun hmem ↦
    let ⟨i, hi, hvi⟩ := Set.mem_iUnion₂.1 hmem
    (Finset.mem_filter.1 ((hv i (hsx hi)).1 hvi)).2 hi
  obtain ⟨q₀, hq₀, hvq₀⟩ : ∃ q₀ ∈ C, v ∉ q₀ := by
    by_contra hcon
    push Not at hcon
    exact hvs (by rw [hs]; exact ⟨hvφ, Set.mem_sInter.2 hcon⟩)
  obtain ⟨s₀, -, hs₀x, rfl⟩ := Set.mem_supClosure_image.1 (hC hq₀)
  have hs₀ : ⋃ k ∈ s₀, p k = (⋃ i ∈ I, p i) ∩ ⋂₀ C :=
    Set.Subset.antisymm (hs ▸ Set.biUnion_subset_biUnion_left (s := (s₀ : Set ι))
      (s' := (s : Set ι)) fun k hk ↦ by_contra fun hks ↦ hvq₀ (Set.mem_biUnion hk
        ((hv k (hs₀x hk)).2 (Finset.mem_filter.2 ⟨hs₀x hk, hks⟩))))
      (Set.inter_subset_right.trans (Set.sInter_subset_of_mem hq₀))
  have hnIE := hIE (⋃ k ∈ s₀, p k)
  rw [isInnocentlyExcludable_iff_exhMW_subset_compl C _ _ hq₀, Set.not_subset] at hnIE
  obtain ⟨u, hu, huq⟩ := hnIE
  exact hvq₀ (hu.2 hvφ (fun q hq ↦ ⟨hq.1, Set.mem_sInter.1
    (hs₀ ▸ not_not.1 huq : u ∈ (⋃ i ∈ I, p i) ∩ ⋂₀ C).2 q hq.1⟩) ⟨hq₀, not_not.1 huq⟩).2

/-- When the disjuncts are independent, the readings pruning derives are the conjunctions of
sub-disjunctions, barring the sub-disjunctions themselves other than the whole disjunction. -/
theorem prunedReadings_eq [DecidableEq ι] (hind : ∀ T ⊆ I, ∃ w, ∀ i ∈ I, w ∈ p i ↔ i ∈ T)
    (hne : I.Nonempty) :
    prunedReadings I p = infClosure (supClosure (p '' I)) \
      (supClosure (p '' I) \ {⋃ i ∈ I, p i}) :=
  Set.Subset.antisymm (fun _ hr ↦ ⟨prunedReadings_subset_infClosure (.of_forall_subset hind) hne hr,
    fun hrS ↦ hrS.2 (eq_biUnion_of_mem_prunedReadings_of_mem_supClosure hind hne hr hrS.1)⟩)
    (infClosure_diff_subset_prunedReadings (.of_forall_subset hind) hne)

/-! ### The reading a question selects -/

variable (I p) in
/-- The reading a partition selects is the strongest derived reading it determines. -/
def IsPrunedReading (Q : Setoid World) (q : Set World) : Prop :=
  IsLeast {r ∈ prunedReadings I p | Q.Determines r} q

theorem IsPrunedReading.unique {Q : Setoid World} {q r : Set World} (hq : IsPrunedReading I p Q q)
    (hr : IsPrunedReading I p Q r) : q = r :=
  IsLeast.unique hq hr

/-- A reading that is the cell of a world where every disjunct holds is the one selected. -/
theorem isPrunedReading_of_cell_eq (h : Separating I p) (hne : I.Nonempty) {Q : Setoid World}
    {q : Set World} (hq : q ∈ prunedReadings I p) {w : World} (hw : w ∈ ⋂ i ∈ I, p i)
    (hQ : Q.cell w = q) : IsPrunedReading I p Q q := by
  subst hQ
  exact ⟨⟨hq, Setoid.determines_cell w⟩, fun _ hr ↦
    hr.2.cell_subset (iInter_subset_of_mem_prunedReadings h hne hr.1 hw)⟩

/-- Every reading is the one selected by the polar question whether it holds. -/
theorem isPrunedReading_polar (h : Separating I p) (hne : I.Nonempty) {q : Set World}
    (hq : q ∈ prunedReadings I p) : IsPrunedReading I p (Setoid.polar q) q := by
  obtain ⟨w, hw⟩ := h.all
  have hw' : w ∈ ⋂ i ∈ I, p i := Set.mem_iInter₂.2 hw
  exact isPrunedReading_of_cell_eq h hne hq hw'
    (Setoid.polar_cell_of_mem (iInter_subset_of_mem_prunedReadings h hne hq hw'))

/-! ### Threshold readings -/

section Count

variable [DecidableEq ι] [∀ w i, Decidable (w ∈ p i)]

theorem atLeastTrue_mem_prunedReadings (h : Separating I p) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ I.card) : atLeastTrue I p k ∈ prunedReadings I p := by
  have hne : I.Nonempty := Finset.card_pos.1 (hk.trans_le hkn)
  have hm : I.card + 1 - k ≤ I.card := by omega
  have hC := subDisjsOfCard_subset_supClosure (p := p) hne
    (by omega : 0 < I.card + 1 - k)
  have he := exhIEII_subDisjsOfCard h (by omega) hm
  rw [show I.card + 1 - (I.card + 1 - k) = k by omega] at he
  refine ⟨_, ⟨hC, ?_⟩, he⟩
  rw [he, exhIEII_supClosure h hne, ← atLeastTrue_card]
  exact atLeastTrue_antitone hkn

theorem isPrunedReading_polar_atLeastTrue (h : Separating I p) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ I.card) :
    IsPrunedReading I p (Setoid.polar (atLeastTrue I p k)) (atLeastTrue I p k) :=
  isPrunedReading_polar h (Finset.card_pos.1 (hk.trans_le hkn))
    (atLeastTrue_mem_prunedReadings h hk hkn)

end Count

end Exhaustification
