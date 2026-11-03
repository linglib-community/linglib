module

public import Linglib.Core.Order.LeftLinear
public import Linglib.Semantics.Tense.Allen
public import Linglib.Semantics.Tense.Defs
public import Linglib.Logic.Modal.Defs

/-!
# Quantificational tense

Read quantificationally, a tense quantifies over the times its cell admits, as in the tense logic
of Prior: `◇[toSetRel ⟦past⟧] P t`, possibility along the cell's relation (`Tense.toSetRel`, and
`Allen.toSetRel` on intervals), says that `P` held at some time before `t`, and `□` that it held at
all of them. Sometime in the past is
[left adjoint to always in the future](##Tense.diamond_past_box_future_gc). The schemas beyond
$K_t$ correspond to the structure of time: $FFp \to Fp$ is [axiom 4](##ModalLogic.diamond_four),
its converse holds [exactly when time is dense](##Tense.diamond_future_den_iff), $Gp \to Fp$
[exactly when time has no last moment](##Tense.isSerial_toSetRel_future_iff), and $PFp \to Mp$
[exactly when time does not branch forward](##Tense.diamond_past_diamond_future_le_iff). A tense
under a tense [entails the tense of the composed cell](##Tense.diamond_diamond_toSetRel), and is
that tense for all cells
[exactly when time is dense without endpoints](##Tense.diamond_toSetRel_comp_iff).

## References

* [prior-1967]
* [burgess-1984]
* [thomason-1984]
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

-- The next five lemmas include the B-series definitions of `P`, `F`, `G` and `H` in [prior-1967]
-- (p. 38).
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

/-- Sometime in the past is left adjoint to always in the future. The unit is the mixing principle
`CpGPp` of [prior-1967] (p. 35), the axiom (A0c) of [burgess-1984], and the counit is Prior's
`CPGpp` (p. 38), Burgess's thesis 3(h) (second edition, p. 9). -/
theorem diamond_past_box_future_gc :
    GaloisConnection (◇[toSetRel ⟦past⟧] : (T → Prop) → T → Prop) □[toSetRel ⟦future⟧] :=
  inv_toSetRel_past (T := T) ▸ diamond_box_gc _

/-- Sometime in the future is left adjoint to always in the past. The unit is the mixing principle
`CpHFp` of [prior-1967] (p. 35), the axiom (A0d) of [burgess-1984], and the counit is Prior's
`CFHpp` (p. 38), the mirror image of Burgess's thesis 3(h). -/
theorem diamond_future_box_past_gc :
    GaloisConnection (◇[toSetRel ⟦future⟧] : (T → Prop) → T → Prop) □[toSetRel ⟦past⟧] :=
  inv_toSetRel_future (T := T) ▸ diamond_box_gc _

/-- Every time has a past exactly when time has no first moment, so that $Hp \to Pp$ holds, the
mirror image of the axiom A2 of [prior-1967] (p. 40). -/
theorem isSerial_toSetRel_past_iff : IsSerial (toSetRel ⟦past⟧ : SetRel T T) ↔ NoMinOrder T :=
  ⟨fun h ↦ ⟨fun t ↦ let ⟨s, hs⟩ := h.serial t; ⟨s, mem_toSetRel_past.1 hs⟩⟩,
    fun h ↦ ⟨fun t ↦ let ⟨s, hs⟩ := h.exists_lt t; ⟨s, mem_toSetRel_past.2 hs⟩⟩⟩

/-- Every time has a future exactly when time has no last moment, so that $Gp \to Fp$ holds, the
axiom A2 of [prior-1967] (p. 38). -/
theorem isSerial_toSetRel_future_iff : IsSerial (toSetRel ⟦future⟧ : SetRel T T) ↔ NoMaxOrder T :=
  ⟨fun h ↦ ⟨fun t ↦ let ⟨s, hs⟩ := h.serial t; ⟨s, mem_toSetRel_future.1 hs⟩⟩,
    fun h ↦ ⟨fun t ↦ let ⟨s, hs⟩ := h.exists_gt t; ⟨s, mem_toSetRel_future.2 hs⟩⟩⟩

/-- Den for the past: a past is a past of a past, $Pp \to PPp$, exactly when time is dense. This is
the mirror image of the axiom A4 of [prior-1967]. -/
theorem diamond_past_den_iff :
    (◇[toSetRel ⟦past⟧] : (T → Prop) → T → Prop) ≤ ◇[toSetRel ⟦past⟧] ∘ ◇[toSetRel ⟦past⟧] ↔
      DenselyOrdered T :=
  diamond_den_iff.trans toSetRel_past_subset_comp_self_iff

/-- Den for the future: a future is a future of a future, $Fp \to FFp$, exactly when time is
dense. This is the axiom A4 of [prior-1967] (pp. 38-39); the modal axiom 4 is his A3. -/
theorem diamond_future_den_iff :
    (◇[toSetRel ⟦future⟧] : (T → Prop) → T → Prop) ≤
        ◇[toSetRel ⟦future⟧] ∘ ◇[toSetRel ⟦future⟧] ↔
      DenselyOrdered T :=
  diamond_den_iff.trans toSetRel_future_subset_comp_self_iff

/-- The quantificational tense of the unconstrained cell is `M` of [prior-1967], true when `P`
holds, will hold or held (p. 38). -/
theorem diamond_toSetRel_top :
    ◇[toSetRel ⊤] P t ↔ ◇[toSetRel ⟦past⟧] P t ∨ P t ∨ ◇[toSetRel ⟦future⟧] P t := by
  simp only [Diamond, mem_toSetRel_top_iff, mem_toSetRel_past, mem_toSetRel_future, or_and_right,
    exists_or, exists_eq_left]

end LT

section PartialOrder

variable [PartialOrder T] {p r : T}

/-- The relation of the unconstrained cell is comparability. -/
theorem mem_toSetRel_top_iff_le : p ~[toSetRel ⊤] r ↔ p ≤ r ∨ r ≤ p := by
  rw [mem_toSetRel_top_iff]
  refine ⟨?_, fun h ↦ h.elim (fun h ↦ ?_) fun h ↦ ?_⟩
  · rintro (h | rfl | h)
    exacts [.inr h.le, .inl le_rfl, .inl h.le]
  · obtain rfl | h := h.eq_or_lt
    exacts [.inr (.inl rfl), .inr (.inr h)]
  · obtain rfl | h := h.eq_or_lt
    exacts [.inr (.inl rfl), .inl h]

/-- $FPp \to Mp$, the form `CFPpAApPpFp` of [prior-1967] (p. 52) and the axiom AK8 that
[thomason-1984] reports from Kamp, holds exactly when the predecessors of any time are comparable,
the *trees* of [burgess-1984], with no branching to the left. -/
theorem diamond_future_diamond_past_le_iff :
    (◇[toSetRel ⟦future⟧] ∘ ◇[toSetRel ⟦past⟧] : (T → Prop) → T → Prop) ≤ ◇[toSetRel ⊤] ↔
      IsLeftLinear T := by
  rw [show (◇[toSetRel ⟦future⟧] ∘ ◇[toSetRel ⟦past⟧] : (T → Prop) → T → Prop) = _ from
    (funext (diamond_comp _ _)).symm, diamond_le_diamond_iff]
  refine ⟨fun h ↦ ⟨fun a b c ha hb ↦ ?_⟩, fun h ⟨a, b⟩ ⟨c, h₁, h₂⟩ ↦ ?_⟩
  · obtain rfl | hac := ha.eq_or_lt
    · exact .inr hb
    obtain rfl | hbc := hb.eq_or_lt
    · exact .inl ha
    exact mem_toSetRel_top_iff_le.1 (h ⟨c, mem_toSetRel_future.2 hac, mem_toSetRel_past.2 hbc⟩)
  · exact mem_toSetRel_top_iff_le.2 (h.comparable_of_le_common (mem_toSetRel_future.1 h₁).le
      (mem_toSetRel_past.1 h₂).le)

/-- $PFp \to Mp$, the form `CPFpAApPpFp` of [prior-1967] (p. 52) and the axiom AK7 that
[thomason-1984] reports from Kamp, holds exactly when the successors of any time are comparable,
with no branching to the right. -/
theorem diamond_past_diamond_future_le_iff :
    (◇[toSetRel ⟦past⟧] ∘ ◇[toSetRel ⟦future⟧] : (T → Prop) → T → Prop) ≤ ◇[toSetRel ⊤] ↔
      IsLeftLinear Tᵒᵈ := by
  rw [show (◇[toSetRel ⟦past⟧] ∘ ◇[toSetRel ⟦future⟧] : (T → Prop) → T → Prop) = _ from
    (funext (diamond_comp _ _)).symm, diamond_le_diamond_iff, isLeftLinear_orderDual_iff]
  refine ⟨fun h a b c ha hb ↦ ?_, fun h ⟨a, b⟩ ⟨c, h₁, h₂⟩ ↦ ?_⟩
  · obtain rfl | hac := ha.eq_or_lt
    · exact .inl hb
    obtain rfl | hbc := hb.eq_or_lt
    · exact .inr ha
    exact mem_toSetRel_top_iff_le.1 (h ⟨c, mem_toSetRel_past.2 hac, mem_toSetRel_future.2 hbc⟩)
  · exact mem_toSetRel_top_iff_le.2 (h (mem_toSetRel_past.1 h₁).le (mem_toSetRel_future.1 h₂).le)

/-- Axiom 5 along the unconstrained cell, the law `CMNMpNMp` of [prior-1967] read through
`ModalLogic.box_five_iff`, holds exactly when time branches neither way. -/
theorem isEuclidean_toSetRel_top_iff :
    IsEuclidean (toSetRel ⊤ : SetRel T T) ↔ IsLeftLinear T ∧ IsLeftLinear Tᵒᵈ := by
  rw [isLeftLinear_orderDual_iff]
  refine ⟨fun h ↦ ⟨⟨fun a b c ha hb ↦ ?_⟩, fun a b c ha hb ↦ ?_⟩,
    fun ⟨hl, hr⟩ ↦ ⟨fun w v u hv hu ↦ ?_⟩⟩
  · exact mem_toSetRel_top_iff_le.1 (h.eucl c a b (mem_toSetRel_top_iff_le.2 (.inr ha))
      (mem_toSetRel_top_iff_le.2 (.inr hb)))
  · exact mem_toSetRel_top_iff_le.1 (h.eucl c a b (mem_toSetRel_top_iff_le.2 (.inl ha))
      (mem_toSetRel_top_iff_le.2 (.inl hb)))
  · rw [mem_toSetRel_top_iff_le] at hv hu ⊢
    rcases hv with hv | hv <;> rcases hu with hu | hu
    exacts [hr hv hu, .inr (hu.trans hv), .inl (hv.trans hu), hl.comparable_of_le_common hv hu]

end PartialOrder

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
