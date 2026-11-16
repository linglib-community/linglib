module

public import Linglib.Semantics.Exhaustification.Disjunctive
public import Linglib.Semantics.Questions.Partition.Basic

/-!
# Pruning alternatives under the weakening constraint

Pruning replaces the formal alternatives of a sentence by a subset. Crnič, Chemla and Fox
constrain it to weaken: the result of exhaustifying over the subset must be entailed by the
result over the whole set. Bar-Lev adds that the question under discussion selects, among the
readings so derived, the strongest one it determines, and [every derived reading is selected by
the polar question whether it holds](##isPrunedReading_polar). This is a different
constraint from Fox and Katzir's `IsAllowableRestriction`, which keeps the alternatives that are
relevant one by one.

For a disjunction of separated disjuncts with its closure under disjunction as alternatives, a
pruning weakens [exactly when it makes nothing innocently
excludable](##mem_prunedReadings_iff), so every derived reading is a conjunction of
sub-disjunctions; when the disjuncts are independent the derived readings are [exactly those
conjunctions that are not themselves proper
sub-disjunctions](##prunedReadings_eq), and "at least `k` of the disjuncts hold"
[is among them](##atLeastTrue_mem_prunedReadings) for every `k`. The question whether at least
`k ≥ 2` hold [determines none of the sub-disjunctions](##not_determines_polar_atLeastTrue), so a
restriction to the alternatives that are relevant one by one would prune them all, though some
are needed to derive the reading that question selects.

## Implementation notes

The constraint on pruning is stated twice: `IsLicensedPruning` is the rule, a maximal weakening
restriction with a relevant result, and `IsPrunedReading` is its outcome, the strongest derived
reading the question determines. For a disjunction
[they agree](##isPrunedReading_iff_exists_isLicensedPruning), because two weakening restrictions
weaken together and pruning less gives a stronger reading.

## References

* [crnic-chemla-fox-2015]
* [bar-lev-2021]
* [fox-katzir-2011]
-/

@[expose] public section

namespace Exhaustification

/-! ### The weakening constraint -/

section General

variable {W : Type*} {F : Set (Set W)} {S q r : Set W}

/-- A restriction `A` of the formal alternatives `F` weakens when exhaustifying the sentence over
`A` is entailed by exhaustifying it over `F`. -/
def IsWeakeningRestriction (F A : Set (Set W)) (S : Set W) : Prop :=
  A ⊆ F ∧ exhIEII F S ⊆ exhIEII A S

/-- The readings pruning derives: the results of exhaustifying over a weakening restriction of
the formal alternatives. -/
def prunedReadings (F : Set (Set W)) (S : Set W) : Set (Set W) :=
  (exhIEII · S) '' {A | IsWeakeningRestriction F A S}

theorem subset_of_mem_prunedReadings (hr : r ∈ prunedReadings F S) : r ⊆ S := by
  obtain ⟨A, -, rfl⟩ := hr
  exact fun _ hw ↦ hw.1

theorem exhIEII_subset_of_mem_prunedReadings (hr : r ∈ prunedReadings F S) :
    exhIEII F S ⊆ r := by
  obtain ⟨A, ⟨-, hA⟩, rfl⟩ := hr
  exact hA

theorem exhIEII_mem_prunedReadings : exhIEII F S ∈ prunedReadings F S :=
  ⟨F, ⟨subset_rfl, subset_rfl⟩, rfl⟩

/-- Pruning everything but the sentence itself derives its unstrengthened reading. -/
theorem self_mem_prunedReadings (hS : S ∈ F) (hsat : S.Nonempty) : S ∈ prunedReadings F S :=
  ⟨{S}, ⟨Set.singleton_subset_iff.2 hS, (exhIEII_singleton hsat).symm ▸ fun _ hw ↦ hw.1⟩,
    exhIEII_singleton hsat⟩

/-- The reading a partition selects is the strongest derived reading it determines. -/
def IsPrunedReading (F : Set (Set W)) (S : Set W) (Q : Setoid W) (q : Set W) : Prop :=
  IsLeast {r ∈ prunedReadings F S | Q.Determines r} q

theorem IsPrunedReading.unique {Q : Setoid W} (hq : IsPrunedReading F S Q q)
    (hr : IsPrunedReading F S Q r) : q = r :=
  IsLeast.unique hq hr

/-- A derived reading that is the cell of a world verifying the unpruned reading is the one
selected. -/
theorem isPrunedReading_of_cell_eq {Q : Setoid W} (hq : q ∈ prunedReadings F S) {w : W}
    (hw : w ∈ exhIEII F S) (hQ : Q.cell w = q) : IsPrunedReading F S Q q := by
  subst hQ
  exact ⟨⟨hq, Setoid.determines_cell w⟩, fun _ hr ↦
    hr.2.cell_subset (exhIEII_subset_of_mem_prunedReadings hr.1 hw)⟩

/-- Every derived reading is the one selected by the polar question whether it holds. -/
theorem isPrunedReading_polar (hne : (exhIEII F S).Nonempty) (hq : q ∈ prunedReadings F S) :
    IsPrunedReading F S (Setoid.polar q) q :=
  let ⟨_, hw⟩ := hne
  isPrunedReading_of_cell_eq hq hw
    (Setoid.polar_cell_of_mem (exhIEII_subset_of_mem_prunedReadings hq hw))

/-- A pruning is licensed by a question when it is a maximal weakening restriction of the formal
alternatives whose result the question determines. -/
def IsLicensedPruning (F : Set (Set W)) (S : Set W) (Q : Setoid W) (A : Set (Set W)) : Prop :=
  Maximal (fun A ↦ IsWeakeningRestriction F A S ∧ Q.Determines (exhIEII A S)) A

end General

/-! ### Pruning the sub-disjunctions of a disjunction -/

variable {World ι : Type*} {I : Finset ι} {p : ι → Set World}

theorem exhIEII_supClosure_nonempty (h : Separating I p) (hne : I.Nonempty) :
    (exhIEII (supClosure (p '' I)) (⋃ i ∈ I, p i)).Nonempty :=
  let ⟨w, hw⟩ := h.all
  ⟨w, exhIEII_supClosure h hne ▸ Set.mem_iInter₂.2 hw⟩

theorem iInter_subset_of_mem_prunedReadings (h : Separating I p) (hne : I.Nonempty)
    {r : Set World} (hr : r ∈ prunedReadings (supClosure (p '' I)) (⋃ i ∈ I, p i)) :
    ⋂ i ∈ I, p i ⊆ r :=
  exhIEII_supClosure h hne ▸ exhIEII_subset_of_mem_prunedReadings hr

theorem iInter_mem_prunedReadings (h : Separating I p) (hne : I.Nonempty) :
    ⋂ i ∈ I, p i ∈ prunedReadings (supClosure (p '' I)) (⋃ i ∈ I, p i) :=
  exhIEII_supClosure h hne ▸ exhIEII_mem_prunedReadings

theorem isWeakeningRestriction_iff (h : Separating I p) (hne : I.Nonempty)
    {A : Set (Set World)} :
    IsWeakeningRestriction (supClosure (p '' I)) A (⋃ i ∈ I, p i) ↔
      A ⊆ supClosure (p '' I) ∧ ∀ q, ¬ IsInnocentlyExcludable A (⋃ i ∈ I, p i) q :=
  and_congr_right fun hA ↦ by
    rw [exhIEII_supClosure h hne, iInter_subset_exhIEII_iff hA hne h.all]

section Weakening

variable {A B : Set (Set World)} (h : Separating I p) (hne : I.Nonempty)
  (hA : IsWeakeningRestriction (supClosure (p '' I)) A (⋃ i ∈ I, p i))
  (hB : IsWeakeningRestriction (supClosure (p '' I)) B (⋃ i ∈ I, p i))
include h hne hA

theorem exhIEII_eq_of_isWeakeningRestriction :
    exhIEII A (⋃ i ∈ I, p i) = (⋃ i ∈ I, p i) ∩ ⋂₀ A :=
  exhIEII_eq_inter_sInter hA.1 hne h.all ((isWeakeningRestriction_iff h hne).1 hA).2

include hB

/-- Two weakening restrictions of the sub-disjunctions weaken together. -/
theorem IsWeakeningRestriction.union :
    IsWeakeningRestriction (supClosure (p '' I)) (A ∪ B) (⋃ i ∈ I, p i) :=
  (isWeakeningRestriction_iff h hne).2 ⟨Set.union_subset hA.1 hB.1,
    not_isInnocentlyExcludable_union h.single hA.1 hB.1
      ((isWeakeningRestriction_iff h hne).1 hA).2 ((isWeakeningRestriction_iff h hne).1 hB).2⟩

theorem exhIEII_union :
    exhIEII (A ∪ B) (⋃ i ∈ I, p i) = exhIEII A (⋃ i ∈ I, p i) ∩ exhIEII B (⋃ i ∈ I, p i) := by
  rw [exhIEII_eq_of_isWeakeningRestriction h hne (hA.union h hne hB),
    exhIEII_eq_of_isWeakeningRestriction h hne hA, exhIEII_eq_of_isWeakeningRestriction h hne hB,
    Set.sInter_union]
  ext w
  simp only [Set.mem_inter_iff]
  tauto

/-- Among weakening restrictions, pruning less gives a stronger reading. -/
theorem exhIEII_anti_of_isWeakeningRestriction (hAB : A ⊆ B) :
    exhIEII B (⋃ i ∈ I, p i) ⊆ exhIEII A (⋃ i ∈ I, p i) := by
  rw [exhIEII_eq_of_isWeakeningRestriction h hne hA, exhIEII_eq_of_isWeakeningRestriction h hne hB]
  exact Set.inter_subset_inter_right _ (Set.sInter_subset_sInter hAB)

end Weakening

/-- The reading a question selects is the result of a pruning it licenses: the strongest derived
reading the question determines is what a maximal weakening restriction with a relevant result
yields. -/
theorem isPrunedReading_iff_exists_isLicensedPruning (h : Separating I p) (hne : I.Nonempty)
    {Q : Setoid World} {q : Set World} :
    IsPrunedReading (supClosure (p '' I)) (⋃ i ∈ I, p i) Q q ↔
      ∃ C, IsLicensedPruning (supClosure (p '' I)) (⋃ i ∈ I, p i) Q C ∧
        exhIEII C (⋃ i ∈ I, p i) = q := by
  constructor
  · rintro ⟨⟨⟨C₀, hC₀, rfl⟩, hdet⟩, hleast⟩
    have hfin : {A | IsWeakeningRestriction (supClosure (p '' I)) A (⋃ i ∈ I, p i) ∧
        Q.Determines (exhIEII A (⋃ i ∈ I, p i))}.Finite :=
      (I.finite_toSet.image p).supClosure.finite_subsets.subset fun A hA ↦ hA.1.1
    obtain ⟨C, hC₀C, hC⟩ := hfin.exists_le_maximal ⟨hC₀, hdet⟩
    exact ⟨C, hC, Set.Subset.antisymm
      (exhIEII_anti_of_isWeakeningRestriction h hne hC₀ hC.prop.1 hC₀C)
      (hleast ⟨⟨C, hC.prop.1, rfl⟩, hC.prop.2⟩)⟩
  · rintro ⟨C, hC, rfl⟩
    refine ⟨⟨⟨C, hC.prop.1, rfl⟩, hC.prop.2⟩, ?_⟩
    rintro _ ⟨⟨C', hC', rfl⟩, hdet⟩
    have hU := hC.2 ⟨hC.prop.1.union h hne hC', by
      rw [exhIEII_union h hne hC.prop.1 hC']; exact hC.prop.2.inter hdet⟩ Set.subset_union_left
    exact exhIEII_anti_of_isWeakeningRestriction h hne hC' hC.prop.1
      (Set.subset_union_right.trans hU)

/-- A pruning only weakens exactly when it leaves nothing innocently excludable, and then
exhaustification asserts every alternative it keeps. -/
theorem mem_prunedReadings_iff (h : Separating I p) (hne : I.Nonempty) {r : Set World} :
    r ∈ prunedReadings (supClosure (p '' I)) (⋃ i ∈ I, p i) ↔ ∃ C ⊆ supClosure (p '' I),
      (∀ q, ¬ IsInnocentlyExcludable C (⋃ i ∈ I, p i) q) ∧
        (⋃ i ∈ I, p i) ∩ ⋂₀ C = r := by
  simp only [prunedReadings, IsWeakeningRestriction, Set.mem_image, Set.mem_ofPred_eq,
    exhIEII_supClosure h hne, and_assoc]
  refine exists_congr fun C ↦ and_congr_right fun hC ↦ ?_
  rw [iInter_subset_exhIEII_iff hC hne h.all]
  exact and_congr_right fun hIE ↦ by rw [exhIEII_eq_inter_sInter hC hne h.all hIE]

private theorem inter_sInter_mem_infClosure {S C : Set (Set World)} {φ : Set World} (hφ : φ ∈ S)
    (hfin : C.Finite) (hC : C ⊆ S) : φ ∩ ⋂₀ C ∈ infClosure S := by
  induction C, hfin using Set.Finite.induction_on with
  | empty => simpa using subset_infClosure hφ
  | @insert a C _ _ ih =>
    rw [Set.sInter_insert, Set.inter_left_comm]
    exact infClosed_infClosure (subset_infClosure (hC (Set.mem_insert _ _)))
      (ih ((Set.subset_insert _ _).trans hC))

theorem prunedReadings_subset_infClosure (h : Separating I p) (hne : I.Nonempty) :
    prunedReadings (supClosure (p '' I)) (⋃ i ∈ I, p i) ⊆ infClosure (supClosure (p '' I)) := by
  intro r hr
  obtain ⟨C, hC, -, rfl⟩ := (mem_prunedReadings_iff h hne).1 hr
  exact inter_sInter_mem_infClosure (biUnion_mem_supClosure hne)
    ((I.finite_toSet.image _).supClosure.subset hC) hC

/-- A conjunction of sub-disjunctions that is not itself a proper sub-disjunction is derived by
keeping every sub-disjunction it entails. -/
theorem infClosure_diff_subset_prunedReadings (h : Separating I p) (hne : I.Nonempty) :
    infClosure (supClosure (p '' I)) \ (supClosure (p '' I) \ {⋃ i ∈ I, p i}) ⊆
      prunedReadings (supClosure (p '' I)) (⋃ i ∈ I, p i) := by
  rintro r ⟨⟨t, ht, hts, hrt⟩, hr⟩
  have hrC : (⋃ i ∈ I, p i) ∩ ⋂₀ {q ∈ supClosure (p '' I) | r ⊆ q} = r := by
    refine Set.Subset.antisymm (fun w hw ↦ ?_)
      (Set.subset_inter ?_ (Set.subset_sInter fun _ hq ↦ hq.2))
    · rw [← hrt, Finset.inf'_eq_inf, Finset.inf_set_eq_iInter]
      exact Set.mem_iInter₂.2 fun q hq ↦ Set.mem_sInter.1 hw.2 q
        ⟨hts hq, hrt ▸ Finset.inf'_le id hq⟩
    · obtain ⟨q, hq⟩ := ht
      exact (hrt ▸ Finset.inf'_le id hq).trans (subset_biUnion_of_mem_supClosure (hts hq))
  refine (mem_prunedReadings_iff h hne).2 ⟨_, Set.sep_subset _ _, fun q hIE ↦ ?_, hrC⟩
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
    (hind : ∀ T ⊆ I, T.Nonempty → ∃ w, ∀ i ∈ I, w ∈ p i ↔ i ∈ T) (hne : I.Nonempty) {r : Set World}
    (hr : r ∈ prunedReadings (supClosure (p '' I)) (⋃ i ∈ I, p i)) (hrS : r ∈ supClosure (p '' I)) :
    r = ⋃ i ∈ I, p i := by
  obtain ⟨C, hC, hIE, rfl⟩ := (mem_prunedReadings_iff (.of_forall_subset hind hne) hne).1 hr
  obtain ⟨s, -, hsx, hs⟩ := Set.mem_supClosure_image.1 hrS
  by_contra hneq
  obtain ⟨j, hj, hjs⟩ : ∃ j ∈ I, j ∉ s := by
    by_contra hcon
    push Not at hcon
    exact hneq (Set.Subset.antisymm Set.inter_subset_left
      (hs ▸ Set.biUnion_subset_biUnion_left (s := (I : Set ι))
        (s' := (s : Set ι)) fun j hj ↦ hcon j hj))
  obtain ⟨v, hv⟩ := hind (I.filter (· ∉ s)) (Finset.filter_subset _ _)
    ⟨j, Finset.mem_filter.2 ⟨hj, hjs⟩⟩
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
theorem prunedReadings_eq [DecidableEq ι]
    (hind : ∀ T ⊆ I, T.Nonempty → ∃ w, ∀ i ∈ I, w ∈ p i ↔ i ∈ T) (hne : I.Nonempty) :
    prunedReadings (supClosure (p '' I)) (⋃ i ∈ I, p i) = infClosure (supClosure (p '' I)) \
      (supClosure (p '' I) \ {⋃ i ∈ I, p i}) :=
  Set.Subset.antisymm (fun _ hr ↦
    ⟨prunedReadings_subset_infClosure (.of_forall_subset hind hne) hne hr, fun hrS ↦
      hrS.2 (eq_biUnion_of_mem_prunedReadings_of_mem_supClosure hind hne hr hrS.1)⟩)
    (infClosure_diff_subset_prunedReadings (.of_forall_subset hind hne) hne)

/-! ### Threshold readings -/

section Count

variable [DecidableEq ι] [∀ w i, Decidable (w ∈ p i)]

theorem atLeastTrue_mem_prunedReadings (h : Separating I p) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ I.card) :
    atLeastTrue I p k ∈ prunedReadings (supClosure (p '' I)) (⋃ i ∈ I, p i) := by
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
    IsPrunedReading (supClosure (p '' I)) (⋃ i ∈ I, p i) (Setoid.polar (atLeastTrue I p k))
      (atLeastTrue I p k) :=
  isPrunedReading_polar (exhIEII_supClosure_nonempty h (Finset.card_pos.1 (hk.trans_le hkn)))
    (atLeastTrue_mem_prunedReadings h hk hkn)

omit [DecidableEq ι] in
/-- The question whether at least `k ≥ 2` of the disjuncts hold determines no sub-disjunction,
so keeping only the alternatives that are relevant one by one prunes them all. -/
theorem not_determines_polar_atLeastTrue (h : Separating I p) (hnone : ∃ w, ∀ i ∈ I, w ∉ p i)
    {k : ℕ} (hk : 2 ≤ k) {q : Set World} (hq : q ∈ supClosure (p '' I)) :
    ¬ (Setoid.polar (atLeastTrue I p k)).Determines q := by
  intro hdet
  obtain ⟨S, ⟨a, ha⟩, hS, rfl⟩ := Set.mem_supClosure_image.1 hq
  obtain ⟨w, hw⟩ := h.single a (hS ha)
  obtain ⟨v, hv⟩ := hnone
  have hwk : w ∉ atLeastTrue I p k := by
    have h1 : trueCount I p w = 1 := Finset.card_eq_one.2 ⟨a, Finset.ext fun j ↦ by
      rw [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun ⟨hj, hwj⟩ ↦ (hw j hj).1 hwj, fun hja ↦ hja ▸ ⟨hS ha, (hw a (hS ha)).2 rfl⟩⟩⟩
    rw [mem_atLeastTrue, h1]
    omega
  have hvk : v ∉ atLeastTrue I p k := fun hvk ↦
    let ⟨i, hi, hvi⟩ := Set.mem_iUnion₂.1 (trueCount_pos.1 (lt_of_lt_of_le (by omega) hvk))
    hv i hi hvi
  obtain ⟨i, hi, hvi⟩ := Set.mem_iUnion₂.1 ((hdet.iff (w := w) (v := v)
    (Setoid.polar_iff.2 (iff_of_false hwk hvk))).1 (Set.mem_biUnion ha ((hw a (hS ha)).2 rfl)))
  exact hv i (hS hi) hvi

end Count

end Exhaustification
