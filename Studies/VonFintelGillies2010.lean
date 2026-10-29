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
them. A subject matter is a `Setoid`, and a proposition is an issue in it when the setoid decides
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
abbrev noWetGear : World → Prop := (·.1 = false)

/-- (25b) `Q`: it is raining. -/
abbrev raining : World → Prop := (·.2 = true)

/-- `P ∪ Q`: rain gear is wet only if it is raining. -/
abbrev onlyRainWets : World → Prop := fun w ↦ noWetGear w ∨ raining w

/-- `W \ P`: there is wet rain gear. -/
abbrev wetGear : World → Prop := fun w ↦ ¬ noWetGear w

/-- The kernel `{P ∪ Q, W \ P}` of Figure 3(a): wet rain gear, with rain its only cause. -/
def wetGearK : Kernel World := ⟨{onlyRainWets, wetGear}⟩

/-- The kernel `{P ∪ Q, Q}` of Figure 3(b): the rain itself. -/
def rainK : Kernel World := ⟨{onlyRainWets, raining}⟩

/-- A one-proposition kernel, rain the only cause of wet gear, whose base properly contains
`⟦raining⟧`. -/
def onlyRainWetsK : Kernel World := ⟨{onlyRainWets}⟩

theorem wetGearK_base : wetGearK.base = ({(true, true)} : Set World) := by
  ext w
  rcases w with ⟨_ | _, _ | _⟩ <;> simp [wetGearK]

theorem raining_unsettled : ¬ wetGearK.directlySettles raining := by
  rintro ⟨x, hx, hxor⟩
  rcases hx with rfl | hx'
  · rcases hxor with h_sub | h_disj
    · exact (show ¬ raining (false, false) from by decide)
        (h_sub (show onlyRainWets (false, false) from by decide))
    · exact Set.disjoint_left.mp h_disj (show onlyRainWets (true, true) from by decide)
        (show raining (true, true) from by decide)
  · obtain rfl : x = wetGear := hx'
    rcases hxor with h_sub | h_disj
    · exact (show ¬ raining (true, false) from by decide)
        (h_sub (show wetGear (true, false) from by decide))
    · exact Set.disjoint_left.mp h_disj (show wetGear (true, true) from by decide)
        (show raining (true, true) from by decide)

theorem raining_follows : wetGearK.FollowsFrom raining := by
  rw [Kernel.followsFrom_iff, wetGearK_base]
  rintro w rfl
  rfl

theorem must_raining_eq_one (w : World) : kernelMust wetGearK raining w = 1 :=
  kernelMust_eq_one_iff.2 ⟨raining_unsettled, raining_follows⟩

theorem rainK_settles_raining : rainK.directlySettles raining :=
  ⟨raining, by simp [rainK], Or.inl subset_rfl⟩

/-! ### Deep theorems -/

theorem entailment_settling_gap :
    ∃ (k : Kernel World) (φ : World → Prop),
      k.FollowsFrom φ ∧ ¬ k.directlySettles φ :=
  ⟨wetGearK, raining, raining_follows, raining_unsettled⟩

-- §4.1, (6), (7)
theorem indirectness_neq_weakness (w : World) :
    kernelMust wetGearK raining w = 1 ∧ kernelMust rainK raining w = 0 ∧
      kernelMust onlyRainWetsK raining w = -1 := by
  refine ⟨must_raining_eq_one w, kernelMust_eq_zero_iff.2 rainK_settles_raining,
    kernelMust_eq_neg_one_iff.2 ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, hxor⟩
    obtain rfl : x = onlyRainWets := hx
    rcases hxor with h_sub | h_disj
    · exact (show ¬ raining (false, false) from by decide)
        (h_sub (show onlyRainWets (false, false) from by decide))
    · exact Set.disjoint_left.mp h_disj (show onlyRainWets (true, true) from by decide)
        (show raining (true, true) from by decide)
  · intro h
    have hw : ((false, false) : World) ∈ onlyRainWetsK.base :=
      Kernel.mem_base.mpr fun p hp ↦ by
        obtain rfl : p = onlyRainWets := hp; decide
    exact (by decide : ¬ raining (false, false)) (h _ hw)

variable {W : Type*} (k : Kernel W)

theorem modus_ponens_with_must (φ ψ : W → Prop) (w : W)
    (hReal : w ∈ k.base)
    (hCond : φ w → kernelMust k ψ w = 1)
    (hPhi : φ w) :
    ψ w :=
  Modality.must_entails_prejacent k ψ w hReal (kernelMust_eq_one_iff.1 (hCond hPhi)).2

theorem must_perhaps_contradiction (φ : W → Prop) (w : W)
    (hMust : kernelMust k φ w = 1) :
    kernelMight k (fun w' ↦ ¬ φ w') w = -1 := by
  obtain ⟨hs, hf⟩ := kernelMust_eq_one_iff.1 hMust
  refine kernelMight_eq_neg_one_iff.2 ⟨(Kernel.directlySettles_not k φ).not.2 hs, ?_⟩
  rintro ⟨w', hw', hφneg⟩
  exact hφneg (hf w' hw')

/-! ### Implementation 2: settling by partitions (Definition 7, §7.2)

Def 7 presents subject matters as equivalence relations on `W`: `S[P]` keeps
the pairs of `S` that agree on `P`, and `P` is an *issue* in `S` iff
`S[P] = S`. The subject matter S_K determined by a kernel is the refinement
`S_o[P₁]…[Pₙ]` of the universal relation along each kernel proposition —
equivalently, the relation "agrees on every `X ∈ K`". Implementation 2:
K directly settles P iff P is an issue in S_K. -/

/-- The subject matter `S_K` of a kernel, relating worlds that agree on every
    proposition in `K`. -/
def subjectMatter : Setoid W where
  r w v := ∀ p ∈ k.props, (p w ↔ p v)
  iseqv := ⟨fun _ _ _ ↦ Iff.rfl, fun h p hp ↦ (h p hp).symm,
    fun h h' p hp ↦ (h p hp).trans (h' p hp)⟩

/-- `P` is an *issue* in a subject matter `S` when `S`-equivalent worlds never
    disagree on `P`. -/
def IsIssue (s : Setoid W) (φ : W → Prop) : Prop := s.Decides {w | φ w}

/-- `K` settles `P` by partition iff `P` is an issue in `S_K`. -/
def settlesByPartition (φ : W → Prop) : Prop :=
  IsIssue (subjectMatter k) φ

theorem subjectMatter_rel_base {v w : W} (hv : v ∈ k.base) (hw : w ∈ k.base) :
    (subjectMatter k).r v w := fun p hp ↦
  iff_of_true (Kernel.mem_base.mp hv p hp) (Kernel.mem_base.mp hw p hp)

theorem partition_implies_entailment (φ : W → Prop)
    (h : settlesByPartition k φ) :
    k.FollowsFrom φ ∨ k.FollowsFrom (fun w ↦ ¬ φ w) := by
  rcases Set.eq_empty_or_nonempty k.base with hEmpty | ⟨w₀, hw₀⟩
  · exact Or.inl fun w hw ↦ absurd (hEmpty ▸ hw) (Set.notMem_empty w)
  · exact (Classical.em (φ w₀)).imp
      (fun hφ v hv ↦ (Setoid.decides_iff.1 h w₀ v (subjectMatter_rel_base k hw₀ hv)).mp hφ)
      (fun hφ v hv hφv ↦
        hφ ((Setoid.decides_iff.1 h w₀ v (subjectMatter_rel_base k hw₀ hv)).mpr hφv))

/-! ### Non-equivalence of the two implementations (§7.2)

Implementation 1 settles supersets of K-propositions that Implementation 2 misses: `K = {P}`
settles `P ∪ Q` explicitly, but worlds agreeing on `P` disagree on `P ∪ Q`. Implementation 2
settles propositions that K-propositions determine jointly while no single one settles them: the
base of the wet-gear kernel. Under both, the wet rain gear leaves the weather unsettled while
entailing it. -/

private theorem not_settles_onlyRainWets :
    ¬ settlesByPartition ⟨{noWetGear}⟩ onlyRainWets := by
  intro h
  have h' := Setoid.decides_iff.1 h (true, true) (true, false) (fun p hp ↦ by
    obtain rfl : p = noWetGear := hp; decide)
  exact absurd (h'.mp (by decide)) (by decide)

-- §7.2
theorem explicit_not_implies_partition :
    ∃ (k : Kernel World) (φ : World → Prop),
      k.directlySettles φ ∧ ¬ settlesByPartition k φ :=
  ⟨⟨{noWetGear}⟩, onlyRainWets, ⟨noWetGear, by simp, Or.inl fun _ hw ↦ Or.inl hw⟩,
    not_settles_onlyRainWets⟩

theorem partition_not_implies_explicit :
    ∃ (k : Kernel World) (φ : World → Prop),
      settlesByPartition k φ ∧ ¬ k.directlySettles φ := by
  refine ⟨wetGearK, fun w ↦ wetGear w ∧ raining w, Setoid.decides_iff.2 fun w v h ↦ ?_, ?_⟩
  · have h1 := h onlyRainWets (by simp [wetGearK])
    have h2 := h wetGear (by simp [wetGearK])
    revert h1 h2
    rcases w with ⟨_ | _, _ | _⟩ <;> rcases v with ⟨_ | _, _ | _⟩ <;> decide
  · rintro ⟨x, hx, hxor⟩
    rcases hx with rfl | hx'
    · rcases hxor with h_sub | h_disj
      · exact (show ¬ (wetGear (false, false) ∧ raining (false, false)) from by decide)
          (h_sub (show onlyRainWets (false, false) from by decide))
      · exact Set.disjoint_left.mp h_disj (show onlyRainWets (true, true) from by decide)
          (show wetGear (true, true) ∧ raining (true, true) from by decide)
    · obtain rfl : x = wetGear := hx'
      rcases hxor with h_sub | h_disj
      · exact (show ¬ (wetGear (true, false) ∧ raining (true, false)) from by decide)
          (h_sub (show wetGear (true, false) from by decide))
      · exact Set.disjoint_left.mp h_disj (show wetGear (true, true) from by decide)
          (show wetGear (true, true) ∧ raining (true, true) from by decide)

-- §7.2, Figure 5(a)
theorem entailment_not_implies_partition :
    ∃ (k : Kernel World) (φ : World → Prop),
      k.FollowsFrom φ ∧ ¬ settlesByPartition k φ := by
  refine ⟨wetGearK, raining, raining_follows, fun h ↦ ?_⟩
  have h' := Setoid.decides_iff.1 h (false, true) (false, false) (fun p hp ↦ by
    rcases hp with rfl | rfl <;> decide)
  exact absurd (h'.mp (by decide)) (by decide)

end VonFintelGillies2010
