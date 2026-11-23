module

public import Linglib.Semantics.Evidential.Evidence
public import Mathlib.Order.SetNotation

/-!
# Evidence from kernels of privileged information

A kernel is the set `K : Set (Set W)` of propositions a speaker treats as privileged
information, by direct observation or by trustworthy report; its base is their intersection
`⋂₀ K`. A kernel directly settles `P` when one of its propositions entails `P` or excludes it,
which is stronger than its base doing so: the base may entail `P` though no single proposition
settles it.

A family of kernels `K : W → Set (Set W)`, the speaker's privileged information at each world,
gives an evidence relation, `Evidential.kernelEvidence`. At `w` there is attested or reported
evidence for `P` when some proposition of `K w` entails `P`, the kernel not telling observation
from report, and inferring evidence when the base of `K w` entails `P` while `K w` does not
directly settle it. A kernel true at `w` entails exactly what it gives evidence for there
(`Evidential.sInter_subset_iff_exists_mem_kernelEvidence`), and when every kernel is true at its
own world the evidence of each type is veridical (`Evidential.isVeridical_kernelEvidence`).

## Implementation notes

A kernel is a bare set of propositions, as von Fintel and Gillies define it relative to a
context, so `DirectlySettles` takes one kernel. The evidence relation is world-indexed, since an
evidence relation says where the speaker has evidence; a kernel fixed by the context is the
constant family. A family of kernels is a Kratzer conversational background, and the condition
that each is true at its own world is that the background is realistic.

## References

* [von-fintel-gillies-2010]
* [kratzer-2012]
-/

@[expose] public section

namespace Evidential

variable {W : Type*} {K K' : Set (Set W)} {P : Set W} {w : W}

/-! ### Settling -/

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
