module

public import Linglib.Core.Data.Finset.SetFamily
public import Linglib.Semantics.Exhaustification.InnocentInclusion
public import Linglib.Semantics.Exhaustification.Excluder
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Exhaustification over finite world types

Over a `Fintype` of worlds, with propositions as `Finset`s, innocent excludability and the cell
are decidable, since an alternative is innocently excludable iff it fails at every minimal
world and the minimal worlds form a `Finset` (`minimalWorlds`). `innocent` packages innocent
exclusion as an `Excluder`, and the structural theorems compute `innocent.exh` and
`tolerant.exh` for alternative sets of a given shape. Under the coercion to sets an excluder
is `exh` over the alternatives it selects (`Excluder.coe_exh`), and the innocent excluder is
`exhIE` (`coe_innocent_exh`). The maximal consistent exclusions of a finite family are decided
over its subfamilies (`IsMaximalExclusion`, `isMaximalExclusion_iff`).
`preFilter_can_create_implicature` witnesses that removing a symmetric alternative before
exclusion strengthens the result.

## References

* [fox-2007]
* [spector-2016]
* [chierchia-2013]
* [fox-katzir-2011]
-/

@[expose] public section

namespace Exhaustification

variable {W : Type*}

section MaximalExclusion

variable [DecidableEq W]

theorem isConsistentExclusion_asSetOfSets_iff {ALT M : Finset (Finset W)} {φ : Finset W} :
    IsConsistentExclusion ALT.toSetFamily ↑φ M.toSetFamily ↔
      M ⊆ ALT ∧ (φ.filter fun w ↦ ∀ q ∈ M, w ∉ q).Nonempty := by
  refine and_congr Finset.toSetFamily_subset_toSetFamily ⟨?_, ?_⟩
  · rintro ⟨w, hwφ, hw⟩
    exact ⟨w, Finset.mem_filter.2 ⟨hwφ, fun q hq hwq ↦
      hw ⟨_, Finset.mem_toSetFamily.2 ⟨q, hq, rfl⟩, hwq⟩⟩⟩
  · rintro ⟨w, hw⟩
    obtain ⟨hwφ, hwM⟩ := Finset.mem_filter.1 hw
    refine ⟨w, hwφ, fun ⟨s, hs, hws⟩ ↦ ?_⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_toSetFamily.1 hs
    exact hwM q hq hws

/-- A subfamily `M` of `ALT` is a maximal consistent exclusion when denying its members is
consistent with `φ` and denying any larger subfamily is not. -/
def IsMaximalExclusion (ALT : Finset (Finset W)) (φ : Finset W) (M : Finset (Finset W)) : Prop :=
  M ⊆ ALT ∧ (φ.filter fun w ↦ ∀ q ∈ M, w ∉ q).Nonempty ∧
    ∀ M' ∈ ALT.powerset, M ⊂ M' → ¬ (φ.filter fun w ↦ ∀ q ∈ M', w ∉ q).Nonempty

instance (ALT : Finset (Finset W)) (φ : Finset W) (M : Finset (Finset W)) :
    Decidable (IsMaximalExclusion ALT φ M) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ M' ∈ ALT.powerset, _))

theorem isMaximalExclusion_iff {ALT M : Finset (Finset W)} {φ : Finset W} :
    IsMaximalExclusion ALT φ M ↔
      Maximal (IsConsistentExclusion ALT.toSetFamily ↑φ) M.toSetFamily := by
  constructor
  · rintro ⟨hsub, hne, hmax⟩
    refine ⟨isConsistentExclusion_asSetOfSets_iff.2 ⟨hsub, hne⟩, fun Y hY hMY ↦ ?_⟩
    obtain ⟨M', hM', rfl⟩ := Finset.exists_toSetFamily_eq_of_subset hY.1
    rw [Finset.toSetFamily_subset_toSetFamily] at hMY ⊢
    by_contra hnot
    exact hmax M' (Finset.mem_powerset.2 hM') (Finset.ssubset_iff_subset_ne.2
      ⟨hMY, fun h ↦ hnot (h ▸ subset_rfl)⟩) (isConsistentExclusion_asSetOfSets_iff.1 hY).2
  · rintro ⟨hc, hmax⟩
    obtain ⟨hsub, hne⟩ := isConsistentExclusion_asSetOfSets_iff.1 hc
    refine ⟨hsub, hne, fun M' hM' hss hne' ↦ hss.2 ?_⟩
    exact Finset.toSetFamily_subset_toSetFamily.1 (hmax
      (isConsistentExclusion_asSetOfSets_iff.2 ⟨Finset.mem_powerset.1 hM', hne'⟩)
      (Finset.toSetFamily_subset_toSetFamily.2 hss.1))

end MaximalExclusion

variable [Fintype W] [DecidableEq W]

theorem coe_tolerant_exh (ALT : Finset (Finset W)) (φ : Finset W) :
    (↑(tolerant.exh ALT φ) : Set W) = exh ALT.toSetFamily ↑φ := by
  ext w
  simp only [Finset.mem_coe, mem_tolerant_exh_iff, mem_exh, Finset.mem_toSetFamily,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Finset.coe_subset]
  exact and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦
    ⟨fun h hw ↦ not_not.1 fun hs ↦ h hs hw, fun h hs hw ↦ hs (h hw)⟩

theorem Excluder.coe_exh (E : Excluder W) (ALT : Finset (Finset W)) (φ : Finset W)
    (h : ∀ a ∈ E.excluded ALT φ, ¬ φ ⊆ a) :
    (↑(E.exh ALT φ) : Set W) = Exhaustification.exh ((E.excluded ALT φ).toSetFamily) ↑φ := by
  ext w
  rw [Finset.mem_coe, Excluder.mem_exh_iff, Exhaustification.mem_exh]
  refine and_congr_right fun _ ↦ ⟨fun h' q hq hw ↦ ?_, fun h' a ha hw ↦ ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_toSetFamily.1 hq
    exact absurd hw (h' a ha)
  · exact h a ha (Finset.coe_subset.1 (h' ↑a (Finset.mem_toSetFamily.2 ⟨a, ha, rfl⟩) hw))

variable (ALT : Finset (Finset W)) (φ : Finset W)

/-! ### Minimal worlds and innocent excludability -/

/-- The minimal prejacent worlds of a finite family are those where no prejacent world verifies
strictly fewer alternatives. -/
def minimalWorlds : Finset W :=
  φ.filter fun u ↦ ∀ v ∈ φ, (∀ a ∈ ALT, v ∈ a → u ∈ a) → ∀ a ∈ ALT, u ∈ a → v ∈ a

theorem mem_minimalWorlds {u : W} :
    u ∈ minimalWorlds ALT φ ↔ IsMinimal ALT.toSetFamily ↑φ u := by
  rw [minimalWorlds, Finset.mem_filter]
  change _ ↔ (u ∈ (↑φ : Set W) ∧ ¬ ∃ v, v ∈ (↑φ : Set W) ∧ (v <[ALT.toSetFamily] u))
  have hle : ∀ x y : W, (x ≤[ALT.toSetFamily] y) ↔ ∀ a ∈ ALT, x ∈ a → y ∈ a := fun x y ↦
    ⟨fun h a ha ↦ h _ (Finset.mem_toSetFamily.2 ⟨a, ha, rfl⟩), fun h _ hs ↦ by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_toSetFamily.1 hs
      exact h a ha⟩
  simp only [ltALT, hle, Finset.mem_coe, not_exists, not_and, not_not]

/-- The innocently excludable alternatives of a finite family, those false at every minimal
world. -/
def innocentlyExcludable : Finset (Finset W) :=
  ALT.filter fun a ↦ ∀ u ∈ minimalWorlds ALT φ, u ∉ a

theorem innocentlyExcludable_subset (ALT : Finset (Finset W)) (φ : Finset W) :
    innocentlyExcludable ALT φ ⊆ ALT := Finset.filter_subset _ _

theorem isInnocentlyExcludable_iff (a : Finset W) :
    IsInnocentlyExcludable ALT.toSetFamily ↑φ ↑a ↔ a ∈ innocentlyExcludable ALT φ := by
  have haALT : (↑a : Set W) ∈ ALT.toSetFamily ↔ a ∈ ALT := by
    simp only [Finset.mem_toSetFamily, Finset.coe_inj, exists_eq_right]
  rw [innocentlyExcludable, Finset.mem_filter]
  refine ⟨fun h ↦ ⟨haALT.1 h.1, fun u hu ↦ ?_⟩, fun ⟨ha, h⟩ ↦ ?_⟩
  · exact (isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ h.1).1 h
      ((mem_minimalWorlds ALT φ).1 hu)
  · exact (isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ (haALT.2 ha)).2
      fun u hu ↦ h u ((mem_minimalWorlds ALT φ).2 hu)

/-- Innocent excludability is decidable over finite families. -/
instance decidableIsInnocentlyExcludable (a : Finset W) :
    Decidable (IsInnocentlyExcludable ALT.toSetFamily (↑φ) (↑a)) :=
  decidable_of_iff _ (isInnocentlyExcludable_iff ALT φ a).symm

/-! ### The cell -/

/-- The cell of the prejacent, as a `Finset`. -/
def cellFinset : Finset W :=
  Finset.univ.filter fun w =>
    w ∈ φ ∧
    (∀ a ∈ innocentlyExcludable ALT φ, w ∉ a) ∧
    (∀ r ∈ ALT \ innocentlyExcludable ALT φ, w ∈ r)

theorem mem_cellFinset_iff (w : W) :
    w ∈ cellFinset ALT φ ↔ cell ALT.toSetFamily (↑φ) w := by
  unfold cellFinset cell nonExcludable
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, hφ, hexcl, hne⟩
    refine ⟨hφ, ?_, ?_⟩
    · -- IE side: ∀ q with IsInnocentlyExcludable, ¬ q w
      intro q hq
      -- q is a Set; need to recover its Finset form
      have hq_alt : q ∈ ALT.toSetFamily := hq.1
      rcases Finset.mem_toSetFamily.mp hq_alt with ⟨q_f, hq_f_ALT, rfl⟩
      have : q_f ∈ innocentlyExcludable ALT φ :=
        (isInnocentlyExcludable_iff ALT φ q_f).mp hq
      intro hw_q_f
      exact hexcl q_f this hw_q_f
    · rintro r ⟨hr_alt, hr_not_ie⟩
      rcases Finset.mem_toSetFamily.mp hr_alt with ⟨r_f, hr_f_ALT, rfl⟩
      have hr_not_ie_finset : r_f ∉ innocentlyExcludable ALT φ := by
        intro h
        exact hr_not_ie ((isInnocentlyExcludable_iff ALT φ r_f).mpr h)
      exact hne r_f
        (Finset.mem_sdiff.mpr ⟨hr_f_ALT, hr_not_ie_finset⟩)
  · rintro ⟨hφ, hexcl, hne⟩
    refine ⟨Finset.mem_univ _, hφ, ?_, ?_⟩
    · intro a ha hw_a
      have ha_set_ie : IsInnocentlyExcludable
          ALT.toSetFamily (↑φ) (↑a) :=
        (isInnocentlyExcludable_iff ALT φ a).mpr ha
      exact hexcl _ ha_set_ie hw_a
    · intro r hr
      rcases Finset.mem_sdiff.mp hr with ⟨hr_ALT, hr_not_ie⟩
      have hr_set_alt : (↑r : Set W) ∈ ALT.toSetFamily :=
        Finset.mem_toSetFamily.mpr ⟨r, hr_ALT, rfl⟩
      have hr_not_ie_set : ¬ IsInnocentlyExcludable
          ALT.toSetFamily (↑φ) (↑r) := by
        intro h
        exact hr_not_ie ((isInnocentlyExcludable_iff ALT φ r).mp h)
      exact hne (↑r) ⟨hr_set_alt, hr_not_ie_set⟩

/-- The cell is decidable over finite families. -/
instance decidableCell (w : W) :
    Decidable (cell ALT.toSetFamily (↑φ) w) :=
  decidable_of_iff _ (mem_cellFinset_iff ALT φ w)

/-! ### The innocent excluder -/

/-- The innocent excluder of [fox-2007] computes `exhIE` over finite worlds. -/
def innocent {W : Type*} [Fintype W] [DecidableEq W] : Excluder W where
  excluded := innocentlyExcludable
  excluded_subset := innocentlyExcludable_subset

theorem coe_innocent_exh : (↑(innocent.exh ALT φ) : Set W) = exhIE ALT.toSetFamily ↑φ := by
  ext w
  rw [Finset.mem_coe, Excluder.mem_exh_iff, mem_exhIE_iff]
  refine and_congr_right fun _ ↦
    ⟨fun h a ha ↦ ?_, fun h a ha ↦ h ↑a ((isInnocentlyExcludable_iff ALT φ a).2 ha)⟩
  obtain ⟨b, hb, rfl⟩ := Finset.mem_toSetFamily.1 ha.1
  exact h b ((isInnocentlyExcludable_iff ALT φ b).1 ha)

theorem innocent_exh_eq_phi_of_innocentlyExcludable_empty
    {ALT : Finset (Finset W)} {φ : Finset W}
    (h : innocentlyExcludable ALT φ = ∅) :
    innocent.exh ALT φ = φ := by
  show φ \ ((innocentlyExcludable ALT φ).biUnion id) = φ
  rw [h]
  simp

/-! ### Tolerant exhaustification -/

theorem tolerant_exh_eq_empty_of_covered
    {ALT : Finset (Finset W)} {φ : Finset W}
    (h : ∀ w ∈ φ, ∃ α ∈ ALT, ¬ φ ⊆ α ∧ w ∈ α) :
    tolerant.exh ALT φ = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro w hmem
  rw [mem_tolerant_exh_iff] at hmem
  obtain ⟨hw_phi, hw_neg⟩ := hmem
  obtain ⟨α, hα_ALT, hα_neg, hw_α⟩ := h w hw_phi
  exact hw_neg α hα_ALT hα_neg hw_α

theorem covered_of_tolerant_exh_eq_empty
    {ALT : Finset (Finset W)} {φ : Finset W}
    (h : tolerant.exh ALT φ = ∅) (w : W) (hw : w ∈ φ) :
    ∃ α ∈ ALT, ¬ φ ⊆ α ∧ w ∈ α := by
  by_contra hcon
  push Not at hcon
  have hw_exh : w ∈ tolerant.exh ALT φ := by
    rw [mem_tolerant_exh_iff]
    refine ⟨hw, fun α hα_ALT hα_neg hw_α => ?_⟩
    exact hcon α hα_ALT hα_neg hw_α
  simp [h] at hw_exh

theorem tolerant_exh_eq_empty_iff (ALT : Finset (Finset W)) (φ : Finset W) :
    tolerant.exh ALT φ = ∅ ↔ ∀ w ∈ φ, ∃ α ∈ ALT, ¬ φ ⊆ α ∧ w ∈ α :=
  ⟨covered_of_tolerant_exh_eq_empty, tolerant_exh_eq_empty_of_covered⟩

/-! ### Innocent exhaustification -/

theorem tolerant_exh_subset_innocent_exh
    (ALT : Finset (Finset W)) (φ : Finset W) :
    tolerant.exh ALT φ ⊆ innocent.exh ALT φ := by
  intro w hw
  rw [mem_tolerant_exh_iff] at hw
  rw [Excluder.mem_exh_iff]
  obtain ⟨hw_phi, hw_neg⟩ := hw
  refine ⟨hw_phi, fun a ha_ie hw_a => ?_⟩
  have ha_alt : a ∈ ALT := innocentlyExcludable_subset ALT φ ha_ie
  -- a is innocently excludable, so its negation is consistent with φ —
  -- i.e., there is some φ-world outside a. So ¬(φ ⊆ a), and tolerant
  -- negates a. Then if w ∈ a, tolerant would have excluded w, contra.
  apply hw_neg a ha_alt
  · -- ¬ φ ⊆ a: follows from a being innocently excludable.
    intro hsub
    -- Bridge Finset → Set, then apply `not_isInnocentlyExcludable_of_phi_subset`.
    have hSet : IsInnocentlyExcludable
        ALT.toSetFamily (↑φ : Set W) (↑a : Set W) :=
      (isInnocentlyExcludable_iff ALT φ a).mpr ha_ie
    have hfin : Set.Finite ALT.toSetFamily :=
      (Set.toFinite _).image _
    have hsat : ∃ x : W, (↑φ : Set W) x := ⟨w, hw_phi⟩
    have h_subset_set : (↑φ : Set W) ⊆ (↑a : Set W) := fun x hx => hsub hx
    exact not_isInnocentlyExcludable_of_phi_subset
        hfin hsat h_subset_set hSet
  · exact hw_a

theorem innocent_exh_pairwise_disjoint_partial
    {ALT : Finset (Finset W)} {φ : Finset W}
    (hcompat : (φ \ ALT.sup id).Nonempty) :
    innocent.exh ALT φ = φ \ ALT.sup id := by
  -- Step 1: innocentlyExcludable ALT φ = ALT.
  have h_ie_eq : innocentlyExcludable ALT φ = ALT := by
    refine Finset.Subset.antisymm (innocentlyExcludable_subset _ _) ?_
    intro α hα
    rw [← isInnocentlyExcludable_iff]
    apply IsInnocentlyExcludable.of_full_exclusion_consistent
    · exact Finset.mem_toSetFamily.mpr ⟨α, hα, rfl⟩
    · obtain ⟨w, hw⟩ := hcompat
      rw [Finset.mem_sdiff] at hw
      obtain ⟨hw_phi, hw_not_sup⟩ := hw
      refine ⟨w, hw_phi, ?_⟩
      intro b hb
      rcases Finset.mem_toSetFamily.mp hb with ⟨β, hβ_mem, rfl⟩
      intro hw_β
      apply hw_not_sup
      rw [Finset.sup_eq_biUnion]
      exact Finset.mem_biUnion.mpr ⟨β, hβ_mem, hw_β⟩
  -- Step 2: unfold `exh` and convert `biUnion id` to `sup id`.
  show φ \ ((innocentlyExcludable ALT φ).biUnion id) = φ \ ALT.sup id
  rw [h_ie_eq, ← Finset.sup_eq_biUnion]

theorem innocent_exh_singleton {α φ : Finset W} (h : (φ \ α).Nonempty) :
    innocent.exh ({α} : Finset (Finset W)) φ = φ \ α := by
  simpa using innocent_exh_pairwise_disjoint_partial (ALT := {α}) (by simpa)

theorem innocent_exh_eq_self_of_forall_subset {ALT : Finset (Finset W)} {φ : Finset W}
    (h : ∀ a ∈ ALT, φ ⊆ a) : innocent.exh ALT φ = φ := by
  rcases φ.eq_empty_or_nonempty with rfl | hne
  · exact Finset.subset_empty.1 (Excluder.exh_subset_phi _ _ _)
  refine innocent_exh_eq_phi_of_innocentlyExcludable_empty
    (Finset.eq_empty_of_forall_notMem fun a ha => ?_)
  exact not_isInnocentlyExcludable_of_phi_subset (Finset.finite_toSetFamily ALT)
    (hne.imp fun _ h => h) (Finset.coe_subset.2 (h a (innocentlyExcludable_subset ALT φ ha)))
    ((isInnocentlyExcludable_iff ALT φ a).2 ha)

theorem minimalWorlds_erase_of_subset {ALT : Finset (Finset W)} {a φ : Finset W} (h : φ ⊆ a) :
    minimalWorlds (ALT.erase a) φ = minimalWorlds ALT φ := by
  ext u
  simp only [minimalWorlds, Finset.mem_filter, Finset.mem_erase]
  refine and_congr_right fun hu ↦ forall₂_congr fun v hv ↦ ⟨fun H hvu b hb hub ↦ ?_,
    fun H hvu b hb hub ↦ H (fun c hc hvc ↦ ?_) b hb.2 hub⟩
  · by_cases hba : b = a
    · exact hba ▸ h hv
    · exact H (fun c hc hvc ↦ hvu c hc.2 hvc) b ⟨hba, hb⟩ hub
  · by_cases hca : c = a
    · exact hca ▸ h hu
    · exact hvu c ⟨hca, hc⟩ hvc

theorem innocent_exh_erase_entailed
    {ALT : Finset (Finset W)} {a φ : Finset W}
    (h_entails : φ ⊆ a) (hphi_nonempty : φ.Nonempty) :
    innocent.exh ALT φ = innocent.exh (ALT.erase a) φ := by
  suffices h_ie_eq :
      innocentlyExcludable ALT φ
        = innocentlyExcludable (ALT.erase a) φ by
    show φ \ ((innocentlyExcludable ALT φ).biUnion id)
      = φ \ ((innocentlyExcludable (ALT.erase a) φ).biUnion id)
    rw [h_ie_eq]
  obtain ⟨u, hu⟩ := exists_minimal_of_finite ALT.toSetFamily ↑φ (Finset.finite_toSetFamily ALT)
    hphi_nonempty
  have hu' := (mem_minimalWorlds ALT φ).2 hu
  ext b
  simp only [innocentlyExcludable, minimalWorlds_erase_of_subset h_entails, Finset.mem_filter,
    Finset.mem_erase]
  refine ⟨fun ⟨hb, hall⟩ ↦ ⟨⟨fun hba ↦ ?_, hb⟩, hall⟩, fun ⟨⟨_, hb⟩, hall⟩ ↦ ⟨hb, hall⟩⟩
  subst hba
  exact hall u hu' (h_entails (Finset.mem_filter.1 hu').1)

/-! ### Filtering alternatives can strengthen -/


private def cAlt : Finset (Finset Bool) := {{true}, {false}}
private def cPhi : Finset Bool := Finset.univ
private def cPsi : Finset Bool := {false}
private def cPred : Finset Bool → Bool := fun a => decide (a = ({true} : Finset Bool))

private theorem innocent_exh_at_symmetric_pair :
    innocent.exh cAlt cPhi = cPhi := by decide

private theorem preFilter_innocent_exh_at_symmetric_pair :
    (innocent.preFilter cPred).exh cAlt cPhi = cPsi := by decide

theorem preFilter_can_create_implicature :
    ∃ (E : Excluder Bool) (ALT : Finset (Finset Bool)) (φ ψ : Finset Bool)
      (P : Finset Bool → Bool),
      ¬ E.exh ALT φ ⊆ ψ ∧ (E.preFilter P).exh ALT φ ⊆ ψ := by
  refine ⟨innocent, cAlt, cPhi, cPsi, cPred, ?_, ?_⟩
  · rw [innocent_exh_at_symmetric_pair]; decide
  · rw [preFilter_innocent_exh_at_symmetric_pair]

end Exhaustification
