module

public import Linglib.Semantics.Tense.Allen
public import Linglib.Semantics.Tense.Defs
public import Linglib.Logic.Modal.Defs

/-!
# Quantificational tense

Read quantificationally, a tense quantifies over the times its cell admits, as in the tense logic
of Prior. The quantificational tense of a cell is possibility along the cell's relation
(`Tense.toSetRel`, and `Allen.toSetRel` on intervals), so `◇[toSetRel ⟦past⟧] P t` says that `P`
held at some time before `t`, and necessity `□` along the relation says that it held at all of
them. Sometime in the past is
[left adjoint to always in the future](##Tense.diamond_past_box_future_gc). The schemas beyond
$K_t$ correspond to the shape of time: $FFp \to Fp$ is [axiom 4](##ModalLogic.diamond_four) of a
transitive relation, its converse holds
[exactly when time is dense](##Tense.diamond_future_den_iff), and $Gp \to Fp$
[exactly when time has no last moment](##Tense.isSerial_toSetRel_future_iff). A
tense under a tense [entails the tense of the composed cell](##Tense.diamond_diamond_toSetRel), and
is that tense for all cells
[exactly when time is dense without endpoints](##Tense.diamond_toSetRel_comp_iff).

## References

* [prior-1967]
* [blackburn-derijke-venema-2001]
-/

public section

namespace Tense

open ModalLogic
open scoped Denotes
open scoped SetRel

variable {T : Type*} {C D : Finset Ordering} {P : T → Prop} {t : T}

section LT

variable [LT T]

@[simp] theorem diamond_toSetRel_past : ◇[toSetRel ⟦past⟧] P t ↔ ∃ t' < t, P t' := by
  simp [Diamond]

@[simp] theorem diamond_toSetRel_future : ◇[toSetRel ⟦future⟧] P t ↔ ∃ t' > t, P t' := by
  simp [Diamond]

@[simp] theorem diamond_toSetRel_present (P : T → Prop) : ◇[toSetRel ⟦present⟧] P = P :=
  funext fun _ ↦ propext (by simp [Diamond])

@[simp] theorem box_toSetRel_past : □[toSetRel ⟦past⟧] P t ↔ ∀ t' < t, P t' := by
  simp [Box]

@[simp] theorem box_toSetRel_future : □[toSetRel ⟦future⟧] P t ↔ ∀ t' > t, P t' := by
  simp [Box]

/-- Sometime in the past is left adjoint to always in the future. -/
theorem diamond_past_box_future_gc :
    GaloisConnection (◇[toSetRel ⟦past⟧] : (T → Prop) → T → Prop) □[toSetRel ⟦future⟧] :=
  inv_toSetRel_past (T := T) ▸ diamond_box_gc _

/-- Sometime in the future is left adjoint to always in the past. -/
theorem diamond_future_box_past_gc :
    GaloisConnection (◇[toSetRel ⟦future⟧] : (T → Prop) → T → Prop) □[toSetRel ⟦past⟧] :=
  inv_toSetRel_future (T := T) ▸ diamond_box_gc _

/-- Every time has a past exactly when time has no first moment, so that $Hp \to Pp$ holds. -/
theorem isSerial_toSetRel_past_iff : IsSerial (toSetRel ⟦past⟧ : SetRel T T) ↔ NoMinOrder T :=
  ⟨fun h ↦ ⟨fun t ↦ let ⟨s, hs⟩ := h.serial t; ⟨s, mem_toSetRel_past.1 hs⟩⟩,
    fun h ↦ ⟨fun t ↦ let ⟨s, hs⟩ := h.exists_lt t; ⟨s, mem_toSetRel_past.2 hs⟩⟩⟩

/-- Every time has a future exactly when time has no last moment, so that $Gp \to Fp$ holds. -/
theorem isSerial_toSetRel_future_iff : IsSerial (toSetRel ⟦future⟧ : SetRel T T) ↔ NoMaxOrder T :=
  ⟨fun h ↦ ⟨fun t ↦ let ⟨s, hs⟩ := h.serial t; ⟨s, mem_toSetRel_future.1 hs⟩⟩,
    fun h ↦ ⟨fun t ↦ let ⟨s, hs⟩ := h.exists_gt t; ⟨s, mem_toSetRel_future.2 hs⟩⟩⟩

/-- Den for the past: a past is a past of a past, $Pp \to PPp$, exactly when time is dense. -/
theorem diamond_past_den_iff :
    (◇[toSetRel ⟦past⟧] : (T → Prop) → T → Prop) ≤ ◇[toSetRel ⟦past⟧] ∘ ◇[toSetRel ⟦past⟧] ↔
      DenselyOrdered T :=
  diamond_den_iff.trans toSetRel_past_subset_comp_self_iff

/-- Den for the future: a future is a future of a future, $Fp \to FFp$, exactly when time is
dense. -/
theorem diamond_future_den_iff :
    (◇[toSetRel ⟦future⟧] : (T → Prop) → T → Prop) ≤
        ◇[toSetRel ⟦future⟧] ∘ ◇[toSetRel ⟦future⟧] ↔
      DenselyOrdered T :=
  diamond_den_iff.trans toSetRel_future_subset_comp_self_iff

end LT

section LinearOrder

variable [LinearOrder T]

/-- A quantificational tense under another entails the quantificational tense of the composed
cell. -/
theorem diamond_diamond_toSetRel (h : ◇[toSetRel C] (◇[toSetRel D] P) t) :
    ◇[toSetRel (comp D C)] P t :=
  let ⟨_, h₁, u, h₂, hu⟩ := h; ⟨u, toSetRel_comp_subset C D ⟨_, h₁, h₂⟩, hu⟩

/-- The quantificational tense of a composed cell is one quantificational tense under the other,
for all cells, exactly when time is dense without endpoints. -/
theorem diamond_toSetRel_comp_iff :
    (∀ (C D : Finset Ordering) (P : T → Prop),
        ◇[toSetRel (comp D C)] P = ◇[toSetRel C] (◇[toSetRel D] P)) ↔
      DenselyOrdered T ∧ NoMinOrder T ∧ NoMaxOrder T := by
  rw [← toSetRel_comp_iff]
  refine forall₂_congr fun C D ↦
    ⟨fun h ↦ subset_antisymm ?_ ?_, fun h P ↦ by rw [← h, diamond_comp]⟩
  · exact diamond_le_diamond_iff.1 fun P ↦ (diamond_comp _ _ P).le.trans (h P).ge
  · exact diamond_le_diamond_iff.1 fun P ↦ (h P).le.trans (diamond_comp _ _ P).ge

end LinearOrder

end Tense

namespace Allen

open ModalLogic

variable {T : Type*} [LinearOrder T] {π : NonemptyInterval T} {Q : NonemptyInterval T → Prop}

@[simp] theorem diamond_toSetRel_precedes :
    ◇[toSetRel precedes] Q π ↔ ∃ r, r.Precedes π ∧ Q r := by
  simp [Diamond]

/-- Den on intervals: a past is a past of a past exactly when time is dense. -/
theorem diamond_precedes_den_iff :
    (◇[toSetRel precedes] : (NonemptyInterval T → Prop) → NonemptyInterval T → Prop) ≤
        ◇[toSetRel precedes] ∘ ◇[toSetRel precedes] ↔
      DenselyOrdered T :=
  diamond_den_iff.trans toSetRel_precedes_subset_comp_self_iff

/-- On dense time the past of a past is the past on intervals. -/
theorem diamond_precedes_diamond_precedes [DenselyOrdered T] (Q : NonemptyInterval T → Prop) :
    ◇[toSetRel precedes] (◇[toSetRel precedes] Q) = ◇[toSetRel precedes] Q := by
  rw [← diamond_comp, toSetRel_precedes_comp_self]

end Allen
