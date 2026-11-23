module

public import Linglib.Semantics.Evidentiality.Evidence
public import Linglib.Semantics.Modality.Kernel

/-!
# The evidence a kernel gives

A kernel is the set of propositions a speaker treats as privileged information, by direct
observation or by trustworthy report. A family of kernels `K : W → Set (Set W)`, the speaker's
privileged information at each world, gives an evidence relation,
`Evidential.kernelEvidence`. At `w` there is attested or reported evidence for `P` when some
proposition of `K w` entails `P`, the kernel not telling observation from report, and inferring
evidence when the base of `K w` entails `P` while `K w` does not directly settle it. A kernel
true at `w` entails exactly what it gives evidence for there
(`Evidential.sInter_subset_iff_exists_mem_kernelEvidence`), and when every kernel is true at its
own world the evidence of each type is veridical (`Evidential.isVeridical_kernelEvidence`).

Seen as evidentials, epistemic modals mark inference and not report. *Must P* is true where an
inferential evidential has its evidence in the kernel
(`Modality.kernelMust_eq_true_iff_mem_evidence`), and a reportative evidential has none there
(`Modality.notMem_evidence_of_kernelMust_eq_true`).

## Implementation notes

The evidence relation is world-indexed, since an evidence relation says where the speaker has
evidence; a kernel fixed by the context is the constant family. A family of kernels is a Kratzer
conversational background, and the condition that each is true at its own world is that the
background is realistic.

## References

* [von-fintel-gillies-2010]
* [kratzer-2012]
-/

@[expose] public section

namespace Evidential

open Modality

variable {W : Type*} {P : Set W} {w : W}

/-! ### The evidence a kernel gives -/

section Evidence

variable {K : W → Set (Set W)} {t : EvidenceType}

/-- The evidence a family of kernels gives: attested or reported evidence for what one of the
propositions of the kernel entails, and inferring evidence for what its base entails while no
kernel proposition settles it. -/
def kernelEvidence (K : W → Set (Set W)) : EvidenceType → Set W → Set W
  | .attested, P | .reported, P => {w | ∃ X ∈ K w, X ⊆ P}
  | .inferring, P => {w | ⋂₀ K w ⊆ P ∧ ¬ DirectlySettles (K w) P}

@[simp] theorem mem_kernelEvidence_attested :
    w ∈ kernelEvidence K .attested P ↔ ∃ X ∈ K w, X ⊆ P := Iff.rfl

@[simp] theorem mem_kernelEvidence_reported :
    w ∈ kernelEvidence K .reported P ↔ ∃ X ∈ K w, X ⊆ P := Iff.rfl

@[simp] theorem mem_kernelEvidence_inferring :
    w ∈ kernelEvidence K .inferring P ↔ ⋂₀ K w ⊆ P ∧ ¬ DirectlySettles (K w) P := Iff.rfl

theorem sInter_subset_of_mem_kernelEvidence (h : w ∈ kernelEvidence K t P) : ⋂₀ K w ⊆ P := by
  cases t
  · obtain ⟨X, hX, hXP⟩ := h
    exact (Set.sInter_subset_of_mem hX).trans hXP
  · obtain ⟨X, hX, hXP⟩ := h
    exact (Set.sInter_subset_of_mem hX).trans hXP
  · exact h.1

/-- A kernel true at a world entails exactly what it gives evidence for there. -/
theorem sInter_subset_iff_exists_mem_kernelEvidence (hw : w ∈ ⋂₀ K w) :
    ⋂₀ K w ⊆ P ↔ ∃ t, w ∈ kernelEvidence K t P := by
  refine ⟨fun h ↦ ?_, fun ⟨_, h⟩ ↦ sInter_subset_of_mem_kernelEvidence h⟩
  by_cases hd : ∃ X ∈ K w, X ⊆ P
  · exact ⟨.attested, hd⟩
  · refine ⟨.inferring, h, ?_⟩
    rintro ⟨X, hX, hXP | hXP⟩
    exacts [hd ⟨X, hX, hXP⟩, Set.disjoint_left.1 hXP (Set.sInter_subset_of_mem hX hw) (h hw)]

/-- When every kernel is true at its own world, the evidence of each type is veridical. -/
theorem isVeridical_kernelEvidence (hK : ∀ w, w ∈ ⋂₀ K w) (t : EvidenceType) :
    IsVeridical (kernelEvidence K t) :=
  fun _ w h ↦ sInter_subset_of_mem_kernelEvidence h (hK w)

end Evidence

end Evidential

namespace Modality

open Evidential

variable {W : Type*} {K : Set (Set W)} {P : Set W} {w : W}

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
