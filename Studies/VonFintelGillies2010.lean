module

public import Linglib.Semantics.Modality.Kernel
public import Linglib.Semantics.Questions.Partition.Basic
public import Linglib.Data.Examples.VonFintelGillies2010

/-!
# von Fintel & Gillies (2010): Must … Stay … Strong!

This file formalizes von Fintel and Gillies's defense of a strong epistemic *must* against
the Mantra that *must φ* is weaker than its prejacent, Karttunen's problem (2). On the paper's
analysis *must* stays at the top of the scale of epistemic strength (1) and entails its
prejacent, and the felt weakness is an evidential presupposition: the kernel of direct
information must not directly settle the prejacent, though its modal base may entail it. The
kernel apparatus, the explicit-representation implementation of settling (§7.1) and the
presuppositional operators (Definitions 4 to 6), is `Semantics/Modality/Kernel.lean`; this file
carries the kernels of Billy's weather reports (Figure 3). When she sees wet rain gear and knows
rain is its only cause (`wetGearK`), *it must be raining* is defined and true; when she sees the
rain (`rainK`) it is undefined; and when she knows only the cause (`onlyRainWetsK`) it is defined
and false, so that indirectness and weakness come apart (§4.1). The file also carries the
validity of *if φ, must ψ; φ; so ψ* (Argument 4.3.1), the contradictoriness of *must φ but
perhaps not φ* (Argument 4.3.2), and the second implementation of settling by the partition a
kernel induces, a subject matter in which the prejacent is an issue (Definition 7, §7.2), under
which the wet rain gear again leaves the weather unsettled while entailing it
(`entailment_not_implies_partition`). The two implementations are not equivalent. The paper's
boundary case, a kernel `{P}` that settles `P ∪ Q` explicitly but not by partition, shows one
direction (`explicit_not_implies_partition`); the base of the wet-gear kernel, which its
partition settles and no single kernel proposition does, shows the other
(`partition_not_implies_explicit`), a case the paper does not discuss.

## Implementation notes

The four worlds are the combinations of whether the rain gear coming inside is wet and whether it
is raining, with `P` (no wet rain gear) and `Q` (it is raining) of (25) the propositions
`noWetGear` and `raining`, so that `P ∩ Q` and `P \ Q` are both inhabited, as the figures draw
them. A subject matter is a `Setoid`, and a proposition is an issue in it when the setoid determines
the proposition. The paper's examples are the rows of `Data.Examples.VonFintelGillies2010`.

## References

* [von-fintel-gillies-2010]
* [kratzer-1991]
* [karttunen-1972]
-/

@[expose] public section

namespace VonFintelGillies2010

/-! ### Billy's weather reports (§7.1, Figure 3)

In Figure 3(a) Billy's direct information is that there is wet rain gear (`W \ P`) and that rain
gear gets wet only if it is raining (`P ∪ Q`). Each kernel proposition overlaps `Q` without being
included in it, so neither settles `Q`, while the base, wet gear and rain, entails it. In
Figure 3(b) her direct information is the rain itself (`Q`). -/

open Modality

/-- A world records whether the rain gear coming inside is wet and whether it is raining. -/
abbrev World := Bool × Bool

/-- (25a) `P`: there is no wet rain gear. -/
abbrev noWetGear : Set World := {w | w.1 = false}

/-- (25b) `Q`: it is raining. -/
abbrev raining : Set World := {w | w.2 = true}

/-- `P ∪ Q`: rain gear is wet only if it is raining. -/
abbrev onlyRainWets : Set World := noWetGear ∪ raining

/-- `W \ P`: there is wet rain gear. -/
abbrev wetGear : Set World := noWetGearᶜ

/-- The kernel `{P ∪ Q, W \ P}` of Figure 3(a): wet rain gear, with rain its only cause. -/
def wetGearK : Set (Set World) := {onlyRainWets, wetGear}

/-- The kernel `{P ∪ Q, Q}` of Figure 3(b): the rain itself. -/
def rainK : Set (Set World) := {onlyRainWets, raining}

/-- A one-proposition kernel, rain the only cause of wet gear, whose base properly contains
`raining`. -/
def onlyRainWetsK : Set (Set World) := {onlyRainWets}

theorem sInter_wetGearK : ⋂₀ wetGearK = {(true, true)} := by
  ext ⟨_ | _, _ | _⟩ <;> simp [wetGearK]

theorem raining_unsettled : ¬ DirectlySettles wetGearK raining := by
  simp [DirectlySettles, wetGearK, Set.subset_def, Set.disjoint_left, Prod.forall]

theorem raining_follows : ⋂₀ wetGearK ⊆ raining := by
  simp [sInter_wetGearK]

theorem must_raining_eq_one (w : World) : kernelMust wetGearK raining w = .true :=
  kernelMust_eq_true_iff.2 ⟨raining_unsettled, raining_follows⟩

theorem rainK_settles_raining : DirectlySettles rainK raining :=
  ⟨raining, by simp [rainK], Or.inl subset_rfl⟩

/-! ### Deep theorems -/

theorem entailment_settling_gap :
    ∃ (K : Set (Set World)) (P : Set World), ⋂₀ K ⊆ P ∧ ¬ DirectlySettles K P :=
  ⟨wetGearK, raining, raining_follows, raining_unsettled⟩

-- §4.1, (6), (7)
theorem indirectness_neq_weakness (w : World) :
    kernelMust wetGearK raining w = .true ∧ kernelMust rainK raining w = .undefined ∧
      kernelMust onlyRainWetsK raining w = .false :=
  ⟨must_raining_eq_one w, kernelMust_eq_undefined_iff.2 rainK_settles_raining,
    kernelMust_eq_false_iff.2 (by
      simp [onlyRainWetsK, Set.subset_def, Set.disjoint_left, Prod.forall])⟩

variable {W : Type*} (K : Set (Set W))

theorem modus_ponens_with_must {P Q : Set W} {w : W} (hReal : w ∈ ⋂₀ K)
    (hCond : w ∈ P → kernelMust K Q w = .true) (hP : w ∈ P) : w ∈ Q :=
  (kernelMust_eq_true_iff.1 (hCond hP)).2 hReal

theorem must_perhaps_contradiction {P : Set W} {w : W} (hMust : kernelMust K P w = .true) :
    kernelMight K Pᶜ w = .false :=
  let ⟨hs, hf⟩ := kernelMust_eq_true_iff.1 hMust
  kernelMight_eq_false_iff.2 ⟨directlySettles_compl.not.2 hs, fun ⟨_, hv, hvP⟩ ↦ hvP (hf hv)⟩

/-! ### Implementation 2: settling by partitions (Definition 7, §7.2)

Def 7 presents subject matters as equivalence relations on `W`: `S[P]` keeps
the pairs of `S` that agree on `P`, and `P` is an *issue* in `S` iff
`S[P] = S`. The subject matter S_K determined by a kernel is the refinement
`S_o[P₁]…[Pₙ]` of the universal relation along each kernel proposition —
equivalently, the relation "agrees on every `X ∈ K`". Implementation 2:
K directly settles P iff P is an issue in S_K, that is, S_K determines P. -/

/-- The subject matter `S_K` of a kernel, relating worlds that agree on every
proposition in `K`. -/
def subjectMatter : Setoid W where
  r w v := ∀ X ∈ K, (w ∈ X ↔ v ∈ X)
  iseqv := ⟨fun _ _ _ ↦ Iff.rfl, fun h X hX ↦ (h X hX).symm,
    fun h h' X hX ↦ (h X hX).trans (h' X hX)⟩

/-- `K` settles `P` by partition when `P` is an issue in `S_K`. -/
def SettlesByPartition (P : Set W) : Prop := (subjectMatter K).Determines P

theorem subjectMatter_rel_sInter {v w : W} (hv : v ∈ ⋂₀ K) (hw : w ∈ ⋂₀ K) :
    (subjectMatter K).r v w := fun X hX ↦
  iff_of_true (Set.mem_sInter.1 hv X hX) (Set.mem_sInter.1 hw X hX)

theorem SettlesByPartition.sInter_subset_or {P : Set W} (h : SettlesByPartition K P) :
    ⋂₀ K ⊆ P ∨ ⋂₀ K ⊆ Pᶜ := by
  rcases (⋂₀ K).eq_empty_or_nonempty with hEmpty | ⟨w₀, hw₀⟩
  · exact Or.inl (hEmpty ▸ Set.empty_subset P)
  · exact (em (w₀ ∈ P)).imp
      (fun hP _ hv ↦ (Setoid.determines_iff.1 h w₀ _ (subjectMatter_rel_sInter K hw₀ hv)).mp hP)
      (fun hP _ hv hvP ↦
        hP ((Setoid.determines_iff.1 h w₀ _ (subjectMatter_rel_sInter K hw₀ hv)).mpr hvP))

/-! ### Non-equivalence of the two implementations (§7.2)

Implementation 1 settles supersets of K-propositions that Implementation 2 misses: `K = {P}`
settles `P ∪ Q` explicitly, but worlds agreeing on `P` disagree on `P ∪ Q`. Implementation 2
settles propositions that K-propositions determine jointly while no single one settles them: the
base of the wet-gear kernel. Under both, the wet rain gear leaves the weather unsettled while
entailing it. -/

private theorem not_settles_onlyRainWets : ¬ SettlesByPartition {noWetGear} onlyRainWets := by
  intro h
  have h' := Setoid.determines_iff.1 h (true, true) (true, false) fun X hX ↦ by
    rw [Set.mem_singleton_iff.1 hX]; simp
  simp at h'

-- §7.2
theorem explicit_not_implies_partition :
    ∃ (K : Set (Set World)) (P : Set World), DirectlySettles K P ∧ ¬ SettlesByPartition K P :=
  ⟨{noWetGear}, onlyRainWets, directlySettles_singleton.2 (.inl Set.subset_union_left),
    not_settles_onlyRainWets⟩

theorem partition_not_implies_explicit :
    ∃ (K : Set (Set World)) (P : Set World), SettlesByPartition K P ∧ ¬ DirectlySettles K P := by
  refine ⟨wetGearK, wetGear ∩ raining, Setoid.determines_iff.2 fun w v h ↦ ?_, ?_⟩
  · have h1 := h onlyRainWets (by simp [wetGearK])
    have h2 := h wetGear (by simp [wetGearK])
    revert h1 h2
    rcases w with ⟨_ | _, _ | _⟩ <;> rcases v with ⟨_ | _, _ | _⟩ <;> simp
  · simp [DirectlySettles, wetGearK, Set.subset_def, Set.disjoint_left, Prod.forall]

-- §7.2, Figure 5(a)
theorem entailment_not_implies_partition :
    ∃ (K : Set (Set World)) (P : Set World), ⋂₀ K ⊆ P ∧ ¬ SettlesByPartition K P := by
  refine ⟨wetGearK, raining, raining_follows, fun h ↦ ?_⟩
  have h' := Setoid.determines_iff.1 h (false, true) (false, false) fun X hX ↦ by
    rcases hX with rfl | rfl <;> simp
  simp at h'

end VonFintelGillies2010
