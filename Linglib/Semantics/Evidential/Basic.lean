module

public import Mathlib.Order.Partition.Finpartition
public import Linglib.Semantics.Evidential.Defs

/-!
# Evidential paradigms

This file proves the basic facts about Willett's types of evidence and builds the paradigm a
well-formed inventory forms: its terms partition the parameters the language expresses, a
`Finpartition`. The block of a type is the fiber of `Parameter.evidenceType`
(`EvidenceType.mem_block`), the blocks of the three types are the pairs of parameters
(`EvidenceType.block_attested`, `block_inferring`, `block_reported`), a term is of at most one
type (`IsOfType.eq`), and `evidenceType?` is the type a term is of
(`evidenceType?_eq_some_iff`).

## Main definitions

* `Evidential.finpartition` — the paradigm of a well-formed inventory.

## References

* [aikhenvald-2004]
* [willett-1988]
-/

@[expose] public section

namespace Evidential

@[simp] theorem EvidenceType.mem_block {p : Parameter} {t : EvidenceType} :
    p ∈ t.block ↔ p.evidenceType = t := by
  simp [EvidenceType.block]

@[simp] theorem EvidenceType.block_attested :
    EvidenceType.attested.block = {.visual, .sensory} := by decide

@[simp] theorem EvidenceType.block_inferring :
    EvidenceType.inferring.block = {.inference, .assumption} := by decide

@[simp] theorem EvidenceType.block_reported :
    EvidenceType.reported.block = {.hearsay, .quotative} := by decide

variable {e : Evidential} {t t' : EvidenceType}

/-- A term is of at most one type of evidence. -/
theorem IsOfType.eq (h : e.IsOfType t) (h' : e.IsOfType t') : t = t' := by
  obtain ⟨p, hp⟩ := h.1
  exact (EvidenceType.mem_block.1 (h.2 hp)).symm.trans (EvidenceType.mem_block.1 (h'.2 hp))

theorem evidenceType?_eq_some_iff : e.evidenceType? = some t ↔ e.IsOfType t := by
  unfold evidenceType?
  split_ifs with h₁ h₂ h₃ <;> simp only [Option.some.injEq, false_iff]
  · exact ⟨fun h ↦ h ▸ h₁, fun h ↦ h₁.eq h⟩
  · exact ⟨fun h ↦ h ▸ h₂, fun h ↦ h₂.eq h⟩
  · exact ⟨fun h ↦ h ▸ h₃, fun h ↦ h₃.eq h⟩
  · intro h
    cases t
    exacts [h₁ h, h₃ h, h₂ h]

/-- The paradigm of a well-formed inventory: its terms partition the parameters it expresses. -/
def finpartition (es : List Evidential) (h : WellFormed es) : Finpartition (expressed es) :=
  Finpartition.ofErase (es.map covers).toFinset
    (Finset.supIndep_iff_pairwiseDisjoint.2 fun _ hx _ hy hxy ↦
      (h.map covers fun _ _ ↦ id).forall (List.mem_toFinset.1 hx) (List.mem_toFinset.1 hy) hxy)
    rfl

end Evidential
