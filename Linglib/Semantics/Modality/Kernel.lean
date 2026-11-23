module

public import Linglib.Logic.Trivalent.Proposition
public import Linglib.Semantics.Evidential.Modal

/-!
# Kernel semantics for epistemic modals

Von Fintel and Gillies give epistemic modals an evidential presupposition. The kernel `K` is a set
of propositions, the privileged information, whose intersection `⋂₀ K` is the modal base; the
prejacent must not be directly settled by the kernel, entailed or excluded by one of its
propositions (`Evidential.DirectlySettles`). The presupposition makes *must P* strong, asserting
that `⋂₀ K` entails `P`, while still signalling indirectness, since `⋂₀ K` can entail `P` without
any single kernel proposition settling it. *Might* is the negation of *can't*, presupposition
and all (`Modality.kernelMight_eq_compl_kernelCant`).

Seen as evidentials, epistemic modals mark inference and not report. *Must P* is true where an
inferential evidential has its evidence in the kernel
(`Modality.kernelMust_eq_true_iff_mem_evidence`), and a reportative evidential has none there
(`Modality.notMem_evidence_of_kernelMust_eq_true`). The worked examples are in
`Studies/VonFintelGillies2010.lean`, the *can't* dilemma in `Studies/VonFintelGillies2021.lean`.

## Implementation notes

A kernel is a set of propositions `Set (Set W)` and its modal base is `⋂₀ K`, so no structure
wraps it. The assertion of *must* is Kratzer's simple necessity over the constant modal base `K`,
and the evidence relation of the kernel is that of the constant family `fun _ ↦ K`.

## References

* [von-fintel-gillies-2010]
* [von-fintel-gillies-2021]
-/

@[expose] public section

namespace Modality

open Evidential

variable {W : Type*} {K K' : Set (Set W)} {P : Set W} {w : W}

/-! ### Modal operators -/

open Classical in
/-- *Must P* presupposes that `K` does not directly settle `P` and asserts `⋂₀ K ⊆ P`. -/
noncomputable def kernelMust (K : Set (Set W)) (P : Set W) : W → Trivalent :=
  Trivalent.condEvent (fun _ ↦ ¬ DirectlySettles K P) (fun _ ↦ ⋂₀ K ⊆ P)

open Classical in
/-- *Might P* presupposes that `K` does not directly settle `P` and asserts that `⋂₀ K` meets
`P`. -/
noncomputable def kernelMight (K : Set (Set W)) (P : Set W) : W → Trivalent :=
  Trivalent.condEvent (fun _ ↦ ¬ DirectlySettles K P) (fun _ ↦ (⋂₀ K ∩ P).Nonempty)

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

/-! ### Epistemic modals as evidentials -/

theorem kernelMust_eq_true_iff_mem_kernelEvidence :
    kernelMust K P w = .true ↔ w ∈ kernelEvidence (fun _ ↦ K) .inferring P := by
  simp [and_comm]

variable {e : Evidential}

/-- *Must P* is true exactly where an inferential evidential has its evidence in the kernel. -/
theorem kernelMust_eq_true_iff_mem_evidence (he : e.IsInferential) :
    kernelMust K P w = .true ↔
      w ∈ e.evidence (fun π ↦ kernelEvidence (fun _ ↦ K) π.evidenceType) P := by
  rw [he.evidence_comp, kernelMust_eq_true_iff_mem_kernelEvidence]

/-- Where *must P* is true, a reportative evidential has no evidence in the kernel. -/
theorem notMem_evidence_of_kernelMust_eq_true (he : e.IsReportative)
    (h : kernelMust K P w = .true) :
    w ∉ e.evidence (fun π ↦ kernelEvidence (fun _ ↦ K) π.evidenceType) P := by
  rw [he.evidence_comp]
  rintro ⟨X, hX, hXP⟩
  exact (kernelMust_eq_true_iff.1 h).1 ⟨X, hX, .inl hXP⟩

end Modality
