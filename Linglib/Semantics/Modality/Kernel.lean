module

public import Linglib.Logic.Trivalent.Pointwise
public import Mathlib.Order.SetNotation

/-!
# Kernel semantics for epistemic modals

Von Fintel and Gillies give epistemic modals an evidential presupposition. The kernel `K` is a set
of propositions, the direct information, whose intersection `⋂₀ K` is the modal base; the
prejacent must not be *directly settled* by the kernel, entailed or excluded by one of its
propositions. The presupposition makes *must P* strong, asserting that `⋂₀ K` entails `P`, while
still signalling indirectness, since `⋂₀ K` can entail `P` without any single kernel proposition
settling it. *Might* is [the negation of *can't*](##Modality.kernelMight_eq_compl_kernelCant),
presupposition and all. The worked examples are in `Studies/VonFintelGillies2010.lean`, the
*can't* dilemma in `Studies/VonFintelGillies2021.lean`.

## Implementation notes

A kernel is a set of propositions `Set (Set W)` and its modal base is `⋂₀ K`, so no structure
wraps it. The assertion of *must* is Kratzer's simple necessity over the constant modal base `K`.

## References

* [von-fintel-gillies-2010]
* [von-fintel-gillies-2021]
-/

@[expose] public section

namespace Modality

variable {W : Type*} {K K' : Set (Set W)} {P : Set W} {w : W}

/-! ### Settling ([von-fintel-gillies-2010] §7.1, Implementation 1) -/

/-- A kernel directly settles `P` when one of its propositions entails `P` or excludes it. -/
def DirectlySettles (K : Set (Set W)) (P : Set W) : Prop := ∃ X ∈ K, X ⊆ P ∨ Disjoint X P

/-- What a kernel directly settles its modal base entails or excludes; the converse fails
(`VonFintelGillies2010.entailment_settling_gap`). -/
theorem DirectlySettles.sInter_subset_or (h : DirectlySettles K P) : ⋂₀ K ⊆ P ∨ ⋂₀ K ⊆ Pᶜ :=
  let ⟨_, hX, hXP⟩ := h
  hXP.imp (Set.sInter_subset_of_mem hX).trans
    fun hd ↦ (Set.sInter_subset_of_mem hX).trans hd.subset_compl_right

theorem DirectlySettles.mono (hK : K ⊆ K') (h : DirectlySettles K P) : DirectlySettles K' P :=
  let ⟨X, hX, hXP⟩ := h
  ⟨X, hK hX, hXP⟩

@[simp] theorem directlySettles_singleton {X : Set W} :
    DirectlySettles {X} P ↔ X ⊆ P ∨ Disjoint X P := by
  simp [DirectlySettles]

@[simp] theorem directlySettles_compl : DirectlySettles K Pᶜ ↔ DirectlySettles K P := by
  simp [DirectlySettles, Set.subset_compl_iff_disjoint_right, Set.disjoint_compl_right_iff_subset,
    or_comm]

@[simp] theorem not_directlySettles_empty : ¬ DirectlySettles (∅ : Set (Set W)) P := by
  simp [DirectlySettles]

/-! ### Modal operators ([von-fintel-gillies-2010] Definitions 5 and 6) -/

open Classical in
/-- *Must P* presupposes that `K` does not directly settle `P` and asserts `⋂₀ K ⊆ P`. -/
noncomputable def kernelMust (K : Set (Set W)) (P : Set W) : W → Trivalent :=
  fun _ ↦ .transplication (.ofProp (¬ DirectlySettles K P)) (.ofProp (⋂₀ K ⊆ P))

open Classical in
/-- *Might P* presupposes that `K` does not directly settle `P` and asserts that `⋂₀ K` meets
`P`. -/
noncomputable def kernelMight (K : Set (Set W)) (P : Set W) : W → Trivalent :=
  fun _ ↦ .transplication (.ofProp (¬ DirectlySettles K P)) (.ofProp (⋂₀ K ∩ P).Nonempty)

/-- *Can't P* is *must* `Pᶜ`. -/
noncomputable def kernelCant (K : Set (Set W)) (P : Set W) : W → Trivalent := kernelMust K Pᶜ

@[simp] theorem kernelMust_eq_undefined_iff :
    kernelMust K P w = .undefined ↔ DirectlySettles K P := by
  simp [kernelMust]

@[simp] theorem kernelMust_eq_true_iff :
    kernelMust K P w = .true ↔ ¬ DirectlySettles K P ∧ ⋂₀ K ⊆ P := by
  simp [kernelMust]

@[simp] theorem kernelMust_eq_false_iff :
    kernelMust K P w = .false ↔ ¬ DirectlySettles K P ∧ ¬ ⋂₀ K ⊆ P := by
  simp [kernelMust]

@[simp] theorem kernelMight_eq_undefined_iff :
    kernelMight K P w = .undefined ↔ DirectlySettles K P := by
  simp [kernelMight]

@[simp] theorem kernelMight_eq_true_iff :
    kernelMight K P w = .true ↔ ¬ DirectlySettles K P ∧ (⋂₀ K ∩ P).Nonempty := by
  simp [kernelMight]

@[simp] theorem kernelMight_eq_false_iff :
    kernelMight K P w = .false ↔ ¬ DirectlySettles K P ∧ ¬ (⋂₀ K ∩ P).Nonempty := by
  simp [kernelMight]

/-- *Might* `P` is the negation of *can't* `P`, with the same presupposition and the negated
assertion. -/
theorem kernelMight_eq_compl_kernelCant : kernelMight K P = (kernelCant K P)ᶜ := by
  ext w
  refine Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_ <;>
    simp [kernelCant, Set.subset_compl_iff_disjoint_right, Set.not_disjoint_iff_nonempty_inter]

end Modality
