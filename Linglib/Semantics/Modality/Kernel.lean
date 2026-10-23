module

public import Linglib.Semantics.Modality.Necessity
public import Linglib.Logic.Trivalent.Pointwise

/-!
# Kernel semantics for epistemic modals

Von Fintel and Gillies give epistemic modals an evidential presupposition: the prejacent is not
*directly settled* by the kernel `K`, the direct-information part of the modal base, whose
intersection is the base `B_K`. The presupposition makes *must φ* strong, asserting that `B_K`
entails `φ`, while still signalling indirectness, since `B_K` can entail `φ` without `K`
directly settling it. The partition-based implementation and the worked examples are in
`Studies/VonFintelGillies2010.lean`, the *can't* dilemma in `Studies/VonFintelGillies2021.lean`.

## Main definitions

* `Kernel`: a set of direct-information propositions, with its base `Kernel.base`.
* `Kernel.directlySettles`: some member of the kernel entails or excludes the prejacent.
* `kernelMust`, `kernelMight`, `kernelCant`: the presuppositional operators, trivalent
  propositions undefined where the kernel directly settles the prejacent.

## Main statements

* `explicit_implies_entailment`: direct settling implies entailment, but not conversely.
* `kernelMight_eq_neg_kernelCant`: *might* is the negation of *can't*, presupposition and all.
* `Kernel.followsFrom_iff_simpleNecessity`: the assertion of `kernelMust` is Kratzer's simple
  necessity over the kernel.

## References

* [von-fintel-gillies-2010]
* [von-fintel-gillies-2021]
-/

@[expose] public section

namespace Modality

open Modality

variable {W : Type*}

/-! ### Kernel structure ([von-fintel-gillies-2010] Def 4) -/

/-- A *kernel* is a set of direct-information propositions, determining the
    modal base `B_K = ⋂K` ([von-fintel-gillies-2010] Def 4). -/
structure Kernel (W : Type*) where
  /-- The direct-information propositions K. -/
  props : Set (W → Prop)

variable (k : Kernel W) (φ : W → Prop) (w : W)

namespace Kernel

/-- The modal base `B_K = ⋂K` determined by the kernel. -/
def base : Set W := {w | sInf k.props w}

@[simp] theorem mem_base {k : Kernel W} {w : W} : w ∈ k.base ↔ ∀ p ∈ k.props, p w := by
  simp [base]

/-- The kernel as a context-independent modal base. -/
def toBackground : Background W := fun _ ↦ k.props

/-- `K` is consistent iff `B_K ≠ ∅`. -/
def IsConsistent : Prop := k.base.Nonempty

/-- `φ` follows from `K` iff `B_K ⊆ ⟦φ⟧`. -/
def FollowsFrom : Prop := sInf k.props ≤ φ

/-- `φ` is compatible with `K` iff `B_K ∩ ⟦φ⟧ ≠ ∅`. -/
def compatibleWith : Prop := ∃ w ∈ k.base, φ w

theorem followsFrom_iff : k.FollowsFrom φ ↔ ∀ w ∈ k.base, φ w := Iff.rfl

theorem compatibleWith_iff : k.compatibleWith φ ↔ ∃ w ∈ k.base, φ w := Iff.rfl

end Kernel

/-! ### Settling ([von-fintel-gillies-2010] §7.1, Implementation 1) -/

/-- K directly settles P iff some X ∈ K entails P or is incompatible with P. -/
def Kernel.directlySettles : Prop :=
  ∃ x ∈ k.props,
    {w | x w} ⊆ {w | φ w} ∨ Disjoint {w | x w} {w | φ w}

/-- If `K` directly settles `φ` then `B_K ⊆ ⟦φ⟧` or `B_K ⊆ ⟦¬φ⟧`; the
    converse fails (see `VonFintelGillies2010.entailment_settling_gap`). -/
theorem explicit_implies_entailment (h : k.directlySettles φ) :
    k.FollowsFrom φ ∨ k.FollowsFrom (fun w' ↦ ¬ φ w') := by
  obtain ⟨x, hx_mem, h_sub | h_disj⟩ := h
  · exact Or.inl fun w hw ↦ h_sub (sInf_le hx_mem w hw)
  · exact Or.inr fun w hw ↦ h_disj.subset_compl_right (sInf_le hx_mem w hw)

theorem Kernel.directlySettles_mono {k' : Kernel W} (hk : k.props ⊆ k'.props)
    (h : k.directlySettles φ) :
    k'.directlySettles φ :=
  h.imp fun _ ⟨hm, hx⟩ ↦ ⟨hk hm, hx⟩

@[simp]
theorem Kernel.base_singleton (p : W → Prop) :
    (⟨{p}⟩ : Kernel W).base = {w | p w} := by
  ext; simp

@[simp]
theorem Kernel.directlySettles_singleton (p : W → Prop) :
    (⟨{p}⟩ : Kernel W).directlySettles φ ↔
      {w | p w} ⊆ {w | φ w} ∨ Disjoint {w | p w} {w | φ w} := by
  simp [Kernel.directlySettles]

@[simp]
theorem Kernel.directlySettles_not : k.directlySettles (fun w' ↦ ¬ φ w') ↔ k.directlySettles φ := by
  simp [Kernel.directlySettles, Set.disjoint_left, Set.subset_def, or_comm]

/-! ### Modal operators ([von-fintel-gillies-2010] Defs 5–6) -/

open Classical in
/-- `⟦must φ⟧` presupposes that `K` does not directly settle `φ` and asserts
    `B_K ⊆ ⟦φ⟧`. -/
noncomputable def kernelMust : W → SignType :=
  {_w | ¬ k.directlySettles φ}.indicator fun _ ↦ SignType.ofProp (k.FollowsFrom φ)

open Classical in
/-- `⟦might φ⟧` presupposes that `K` does not directly settle `φ` and asserts
    `B_K ∩ ⟦φ⟧ ≠ ∅`. -/
noncomputable def kernelMight : W → SignType :=
  {_w | ¬ k.directlySettles φ}.indicator fun _ ↦ SignType.ofProp (k.compatibleWith φ)

/-- `⟦can't φ⟧` is `⟦must ¬φ⟧`. -/
noncomputable def kernelCant : W → SignType :=
  kernelMust k (fun w' ↦ ¬ φ w')

variable {k φ w}

@[simp] theorem kernelMust_eq_zero_iff : kernelMust k φ w = 0 ↔ k.directlySettles φ := by
  simp [kernelMust]

@[simp] theorem kernelMust_eq_one_iff :
    kernelMust k φ w = 1 ↔ ¬ k.directlySettles φ ∧ k.FollowsFrom φ := by
  simp [kernelMust]

@[simp] theorem kernelMust_eq_neg_one_iff :
    kernelMust k φ w = -1 ↔ ¬ k.directlySettles φ ∧ ¬ k.FollowsFrom φ := by
  simp [kernelMust]

@[simp] theorem kernelMight_eq_zero_iff : kernelMight k φ w = 0 ↔ k.directlySettles φ := by
  simp [kernelMight]

@[simp] theorem kernelMight_eq_one_iff :
    kernelMight k φ w = 1 ↔ ¬ k.directlySettles φ ∧ k.compatibleWith φ := by
  simp [kernelMight]

@[simp] theorem kernelMight_eq_neg_one_iff :
    kernelMight k φ w = -1 ↔ ¬ k.directlySettles φ ∧ ¬ k.compatibleWith φ := by
  simp [kernelMight]

/-! ### Core properties -/

variable (k φ w)

theorem must_entails_prejacent (hReal : w ∈ k.base) (hTrue : k.FollowsFrom φ) : φ w :=
  hTrue w hReal

theorem Kernel.compatibleWith_iff_not_followsFrom_not :
    k.compatibleWith φ ↔ ¬ k.FollowsFrom fun w' ↦ ¬ φ w' := by
  simp [Kernel.compatibleWith, Kernel.FollowsFrom, Pi.le_def]

theorem kernelMight_eq_neg_kernelCant : kernelMight k φ = -kernelCant k φ := by
  ext w
  refine SignType.eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_ <;>
    simp [kernelCant, Kernel.compatibleWith_iff_not_followsFrom_not]

theorem kernelMust_empty_ne_zero : kernelMust ⟨∅⟩ φ w ≠ 0 := by
  simp [Kernel.directlySettles]

/-! ### Bridge to Kratzer necessity -/

theorem Kernel.followsFrom_iff_simpleNecessity :
    k.FollowsFrom φ ↔ simpleNecessity k.toBackground φ w :=
  Iff.rfl

theorem Kernel.followsFrom_iff_necessity : k.FollowsFrom φ ↔ necessity k.toBackground ⊥ φ w :=
  (k.followsFrom_iff_simpleNecessity φ w).trans (necessity_bot_iff k.toBackground φ w).symm

end Modality
