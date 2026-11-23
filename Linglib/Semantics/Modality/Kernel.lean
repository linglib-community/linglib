module

public import Linglib.Logic.Trivalent.Proposition
public import Linglib.Semantics.Evidential.Evidence
public import Mathlib.Order.SetNotation

/-!
# Kernel semantics for epistemic modals

Von Fintel and Gillies give epistemic modals an evidential presupposition. The kernel `K` is a set
of propositions, the direct information, whose intersection `⋂₀ K` is the modal base; the
prejacent must not be *directly settled* by the kernel, entailed or excluded by one of its
propositions. The presupposition makes *must P* strong, asserting that `⋂₀ K` entails `P`, while
still signalling indirectness, since `⋂₀ K` can entail `P` without any single kernel proposition
settling it. *Might* is [the negation of *can't*](##Modality.kernelMight_eq_compl_kernelCant),
presupposition and all. Seen as evidentials, epistemic modals
mark inference, and not report: a kernel holds what the speaker treats as privileged, by
observation or by trustworthy report, so it gives attested or reported evidence for what one of
its propositions entails and inferring evidence for what its base entails without any of them
settling it (`Modality.kernelEvidence`). A kernel true at the world of evaluation entails exactly
what it gives evidence for (`Modality.sInter_subset_iff_exists_mem_kernelEvidence`), *must P* is
true where an inferential evidential has its evidence
(`Modality.kernelMust_eq_true_iff_mem_evidence`), and a reportative evidential has none there
(`Modality.notMem_evidence_of_kernelMust_eq_true`). The worked examples are in `Studies/VonFintelGillies2010.lean`, the
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

/-! ### The evidence a kernel gives -/

/-- A kernel gives attested or reported evidence for what one of its propositions entails, the
kernel not telling observation from trustworthy report, and inferring evidence for what its
base entails while no kernel proposition settles it. -/
def kernelEvidence (K : Set (Set W)) : Evidential.EvidenceType → Set W → Set W
  | .attested, P | .reported, P => {_w | ∃ X ∈ K, X ⊆ P}
  | .inferring, P => {_w | ⋂₀ K ⊆ P ∧ ¬ DirectlySettles K P}

@[simp] theorem mem_kernelEvidence_attested :
    w ∈ kernelEvidence K .attested P ↔ ∃ X ∈ K, X ⊆ P := Iff.rfl

@[simp] theorem mem_kernelEvidence_reported :
    w ∈ kernelEvidence K .reported P ↔ ∃ X ∈ K, X ⊆ P := Iff.rfl

@[simp] theorem mem_kernelEvidence_inferring :
    w ∈ kernelEvidence K .inferring P ↔ ⋂₀ K ⊆ P ∧ ¬ DirectlySettles K P := Iff.rfl

/-- A kernel true at the world of evaluation entails exactly what it gives evidence for. -/
theorem sInter_subset_iff_exists_mem_kernelEvidence (hw : w ∈ ⋂₀ K) :
    ⋂₀ K ⊆ P ↔ ∃ t, w ∈ kernelEvidence K t P := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_cases hd : ∃ X ∈ K, X ⊆ P
    · exact ⟨.attested, hd⟩
    · refine ⟨.inferring, h, ?_⟩
      rintro ⟨X, hX, hXP | hXP⟩
      exacts [hd ⟨X, hX, hXP⟩, Set.disjoint_left.1 hXP (Set.sInter_subset_of_mem hX hw) (h hw)]
  · rintro ⟨_ | _ | _, h⟩
    · obtain ⟨X, hX, hXP⟩ := h
      exact (Set.sInter_subset_of_mem hX).trans hXP
    · obtain ⟨X, hX, hXP⟩ := h
      exact (Set.sInter_subset_of_mem hX).trans hXP
    · exact h.1

/-- What a kernel true at the world of evaluation gives evidence for holds there. -/
theorem mem_of_mem_kernelEvidence {t : Evidential.EvidenceType} (hw : w ∈ ⋂₀ K)
    (h : w ∈ kernelEvidence K t P) : w ∈ P :=
  (sInter_subset_iff_exists_mem_kernelEvidence hw).2 ⟨t, h⟩ hw

theorem kernelMust_eq_true_iff_mem_kernelEvidence :
    kernelMust K P w = .true ↔ w ∈ kernelEvidence K .inferring P := by
  simp [and_comm]

variable {e : Evidential}

/-- *Must P* is true exactly where an inferential evidential has its evidence in the kernel. -/
theorem kernelMust_eq_true_iff_mem_evidence (he : e.IsInferential) :
    kernelMust K P w = .true ↔
      w ∈ e.evidence (fun π ↦ kernelEvidence K π.evidenceType) P := by
  rw [he.evidence_comp, kernelMust_eq_true_iff_mem_kernelEvidence]

/-- Where *must P* is true, a reportative evidential has no evidence in the kernel. -/
theorem notMem_evidence_of_kernelMust_eq_true (he : e.IsReportative)
    (h : kernelMust K P w = .true) :
    w ∉ e.evidence (fun π ↦ kernelEvidence K π.evidenceType) P := by
  rw [he.evidence_comp]
  rintro ⟨X, hX, hXP⟩
  exact (kernelMust_eq_true_iff.1 h).1 ⟨X, hX, .inl hXP⟩

end Modality
