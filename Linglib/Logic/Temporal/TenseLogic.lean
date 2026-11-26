module

public import Linglib.Core.Order.ForestOrder
public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Temporal.PointAlgebra
public import Linglib.Logic.Temporal.Tense.Basic

/-!
# The point algebra's elements as tense operators

Possibility and necessity along the relations of the point algebra are the operators of tense
logic (`Logic/Temporal/Tense/Basic.lean`): the relation of `{.gt}` is `<`, so `◇[toSetRel {.gt}]`
is `𝐅`, that of `{.lt}` is its converse, so `◇[toSetRel {.lt}]` is `𝐏`, and `◇[toSetRel ⊤]` is
`𝐄`. The correspondences of tense logic are restated for these elements. Two results are about
the algebra itself. Reversing time exchanges the operator of each element with the operator of
its converse, the mirror image of [prior-1967]. One operator under another entails the operator
of the product, and is that operator for all elements exactly when time is dense without
endpoints.

## Main results

* `PointAlgebra.toSetRel_gt_eq`, `PointAlgebra.toSetRel_lt_eq`, `PointAlgebra.toSetRel_top_eq`:
  the relations of the tense operators.
* `PointAlgebra.diamond_toSetRel_toDual`: the mirror image.
* `PointAlgebra.diamond_toSetRel_mul_iff`: operators compose as the algebra's elements do
  exactly on dense time without endpoints.

## Implementation notes

The three equations are not `simp` lemmas: the decidability instance of `x ~[toSetRel C] y` is
found from the form `toSetRel C`. Which element a grammatical tense denotes is said in
`Semantics/Tense/Defs.lean`.

## References

* [prior-1967]
* [burgess-1984]
* [thomason-1984]
* [blackburn-derijke-venema-2001]
-/

public section

namespace PointAlgebra

open ModalLogic
open scoped SetRel

variable {T : Type*} {C D : PointAlgebra} {P : T → Prop} {t : T}

section LT

variable [LT T]

theorem inv_toSetRel_lt : (toSetRel {.lt} : SetRel T T).inv = toSetRel {.gt} := by
  ext ⟨x, y⟩; simp

theorem inv_toSetRel_gt : (toSetRel {.gt} : SetRel T T).inv = toSetRel {.lt} := by
  ext ⟨x, y⟩; simp

/-- The relation of `{.gt}` is precedence, the relation of `𝐅` and `𝐆`. -/
theorem toSetRel_gt_eq : (toSetRel {.gt} : SetRel T T) = {x | x.1 < x.2} := by
  ext ⟨x, y⟩; simp

/-- The relation of `{.lt}` is the converse of precedence, the relation of `𝐏` and `𝐇`. -/
theorem toSetRel_lt_eq : (toSetRel {.lt} : SetRel T T) = {x | x.2 < x.1} := by
  ext ⟨x, y⟩; simp

/-- The relation of the top element is the relation of `𝐄` and `𝐀`. -/
theorem toSetRel_top_eq :
    (toSetRel ⊤ : SetRel T T) = {x | x.2 < x.1 ∨ x.1 = x.2 ∨ x.1 < x.2} := by
  ext ⟨x, y⟩; simp [mem_toSetRel_top, eq_comm]

/-- The mirror image: possibility along an element on reversed time is possibility along its
converse, so a law of tense logic stays a law with past and future exchanged wherever the times
it holds of are closed under reversal ([prior-1967]). -/
theorem diamond_toSetRel_toDual (C : PointAlgebra) (P : T → Prop) (t : T) :
    ◇[toSetRel C] (fun u : Tᵒᵈ ↦ P (OrderDual.ofDual u)) (OrderDual.toDual t) ↔
      ◇[toSetRel C⁻¹] P t :=
  ⟨fun ⟨v, h, hp⟩ ↦ ⟨OrderDual.ofDual v, (mem_toSetRel_toDual C).1 h, hp⟩,
    fun ⟨v, h, hp⟩ ↦ ⟨OrderDual.toDual v, (mem_toSetRel_toDual C).2 h, hp⟩⟩

/-- The mirror image for necessity. -/
theorem box_toSetRel_toDual (C : PointAlgebra) (P : T → Prop) (t : T) :
    □[toSetRel C] (fun u : Tᵒᵈ ↦ P (OrderDual.ofDual u)) (OrderDual.toDual t) ↔
      □[toSetRel C⁻¹] P t :=
  ⟨fun h v hv ↦ h (OrderDual.toDual v) ((mem_toSetRel_toDual C).2 hv),
    fun h v hv ↦ h (OrderDual.ofDual v) ((mem_toSetRel_toDual C).1 hv)⟩

-- The next five lemmas include the B-series definitions of `P`, `F`, `G` and `H` in [prior-1967]
-- (p. 38).
@[simp] theorem diamond_toSetRel_lt : ◇[toSetRel {.lt}] P t ↔ ∃ t' < t, P t' := by
  simp [Diamond]

@[simp] theorem diamond_toSetRel_gt : ◇[toSetRel {.gt}] P t ↔ ∃ t' > t, P t' := by
  simp [Diamond]

@[simp] theorem diamond_toSetRel_one (P : T → Prop) : ◇[toSetRel 1] P = P :=
  funext fun _ ↦ propext (by simp [Diamond])

@[simp] theorem box_toSetRel_lt : □[toSetRel {.lt}] P t ↔ ∀ t' < t, P t' := by
  simp [Box]

@[simp] theorem box_toSetRel_gt : □[toSetRel {.gt}] P t ↔ ∀ t' > t, P t' := by
  simp [Box]

/-- Sometime in the past is left adjoint to always in the future. The unit is the mixing principle
`CpGPp` of [prior-1967] (p. 35), an axiom of the minimal logic in [burgess-1984], and the counit
is Prior's `CPGpp` (p. 38). -/
theorem diamond_lt_box_gt_gc :
    GaloisConnection (◇[toSetRel {.lt}] : (T → Prop) → T → Prop) □[toSetRel {.gt}] :=
  inv_toSetRel_lt (T := T) ▸ diamond_box_gc _

/-- Sometime in the future is left adjoint to always in the past. The unit is the mixing principle
`CpHFp` of [prior-1967] (p. 35), an axiom of the minimal logic in [burgess-1984], and the counit
is Prior's `CFHpp` (p. 38). -/
theorem diamond_gt_box_lt_gc :
    GaloisConnection (◇[toSetRel {.gt}] : (T → Prop) → T → Prop) □[toSetRel {.lt}] :=
  inv_toSetRel_gt (T := T) ▸ diamond_box_gc _

/-- Every time has a past exactly when time has no first moment, so that $Hp \to Pp$ holds, the
mirror image of the axiom A2 of [prior-1967] (p. 40). -/
theorem isSerial_toSetRel_lt_iff : IsSerial (toSetRel {.lt} : SetRel T T) ↔ NoMinOrder T :=
  ⟨fun h ↦ ⟨fun t ↦ let ⟨s, hs⟩ := h.serial t; ⟨s, mem_toSetRel_lt.1 hs⟩⟩,
    fun h ↦ ⟨fun t ↦ let ⟨s, hs⟩ := h.exists_lt t; ⟨s, mem_toSetRel_lt.2 hs⟩⟩⟩

/-- Every time has a future exactly when time has no last moment, so that $Gp \to Fp$ holds, the
axiom A2 of [prior-1967] (p. 38). -/
theorem isSerial_toSetRel_gt_iff : IsSerial (toSetRel {.gt} : SetRel T T) ↔ NoMaxOrder T :=
  ⟨fun h ↦ ⟨fun t ↦ let ⟨s, hs⟩ := h.serial t; ⟨s, mem_toSetRel_gt.1 hs⟩⟩,
    fun h ↦ ⟨fun t ↦ let ⟨s, hs⟩ := h.exists_gt t; ⟨s, mem_toSetRel_gt.2 hs⟩⟩⟩

/-- Den for the past: a past is a past of a past, $Pp \to PPp$, exactly when time is dense. This is
the mirror image of the axiom A4 of [prior-1967]. -/
theorem diamond_lt_den_iff :
    (◇[toSetRel {.lt}] : (T → Prop) → T → Prop) ≤ ◇[toSetRel {.lt}] ∘ ◇[toSetRel {.lt}] ↔
      DenselyOrdered T := by
  rw [toSetRel_lt_eq]
  exact TenseLogic.P_dense_iff

/-- Den for the future: a future is a future of a future, $Fp \to FFp$, exactly when time is
dense. This is the axiom A4 of [prior-1967] (pp. 38-39); the modal axiom 4 is his A3. -/
theorem diamond_gt_den_iff :
    (◇[toSetRel {.gt}] : (T → Prop) → T → Prop) ≤
        ◇[toSetRel {.gt}] ∘ ◇[toSetRel {.gt}] ↔
      DenselyOrdered T := by
  rw [toSetRel_gt_eq]
  exact TenseLogic.F_dense_iff

/-- The quantificational tense of the top element is `M` of [prior-1967], true when `P`
holds, will hold or held (p. 38). -/
theorem diamond_toSetRel_top :
    ◇[toSetRel ⊤] P t ↔ ◇[toSetRel {.lt}] P t ∨ P t ∨ ◇[toSetRel {.gt}] P t := by
  simp only [Diamond, mem_toSetRel_top, mem_toSetRel_lt, mem_toSetRel_gt, or_and_right,
    exists_or, exists_eq_left]

end LT

section PartialOrder

variable [PartialOrder T] {p r : T}

/-- $FPp \to Mp$, the form `CFPpAApPpFp` of [prior-1967] (p. 52) and an axiom that
[thomason-1984] reports from Kamp, holds exactly when the predecessors of any time are comparable,
the *trees* of [burgess-1984], with no branching to the left. -/
theorem diamond_gt_diamond_lt_le_iff :
    (◇[toSetRel {.gt}] ∘ ◇[toSetRel {.lt}] : (T → Prop) → T → Prop) ≤ ◇[toSetRel ⊤] ↔
      IsForestOrder T := by
  rw [toSetRel_gt_eq, toSetRel_lt_eq, toSetRel_top_eq]
  exact TenseLogic.linP_iff_isForestOrder

/-- $PFp \to Mp$, the form `CPFpAApPpFp` of [prior-1967] (p. 52) and an axiom that
[thomason-1984] reports from Kamp, holds exactly when the successors of any time are comparable,
with no branching to the right. -/
theorem diamond_lt_diamond_gt_le_iff :
    (◇[toSetRel {.lt}] ∘ ◇[toSetRel {.gt}] : (T → Prop) → T → Prop) ≤ ◇[toSetRel ⊤] ↔
      IsForestOrder Tᵒᵈ := by
  rw [toSetRel_gt_eq, toSetRel_lt_eq, toSetRel_top_eq]
  exact TenseLogic.linF_iff_isForestOrder

/-- Axiom 5 along the top element, the law `CMNMpNMp` of [prior-1967] read through
`ModalLogic.box_five_iff`, holds exactly when time branches neither way. -/
theorem isEuclidean_toSetRel_top_iff :
    IsEuclidean (toSetRel ⊤ : SetRel T T) ↔ IsForestOrder T ∧ IsForestOrder Tᵒᵈ := by
  rw [isForestOrder_orderDual_iff]
  refine ⟨fun h ↦ ⟨⟨fun a b c ha hb ↦ ?_⟩, fun a b c ha hb ↦ ?_⟩,
    fun ⟨hl, hr⟩ ↦ ⟨fun w v u hv hu ↦ ?_⟩⟩
  · exact mem_toSetRel_top_iff_le.1 (h.eucl c a b (mem_toSetRel_top_iff_le.2 (.inr ha))
      (mem_toSetRel_top_iff_le.2 (.inr hb)))
  · exact mem_toSetRel_top_iff_le.1 (h.eucl c a b (mem_toSetRel_top_iff_le.2 (.inl ha))
      (mem_toSetRel_top_iff_le.2 (.inl hb)))
  · rw [mem_toSetRel_top_iff_le] at hv hu ⊢
    rcases hv with hv | hv <;> rcases hu with hu | hu
    exacts [hr hv hu, .inr (hu.trans hv), .inl (hv.trans hu), hl.le_total_of_le_of_le hv hu]

end PartialOrder

section LinearOrder

variable [LinearOrder T]

/-- A quantificational tense under another entails the quantificational tense of the product. -/
theorem diamond_diamond_toSetRel (h : ◇[toSetRel C] (◇[toSetRel D] P) t) :
    ◇[toSetRel (C * D)] P t :=
  let ⟨_, h₁, u, h₂, hu⟩ := h; ⟨u, toSetRel_comp_subset C D ⟨_, h₁, h₂⟩, hu⟩

/-- The quantificational tense of a product is one quantificational tense under the other, for
all elements of the point algebra, exactly when time is dense without endpoints. -/
theorem diamond_toSetRel_mul_iff :
    (∀ (C D : PointAlgebra) (P : T → Prop),
        ◇[toSetRel (C * D)] P = ◇[toSetRel C] (◇[toSetRel D] P)) ↔
      DenselyOrdered T ∧ NoMinOrder T ∧ NoMaxOrder T := by
  rw [← toSetRel_mul_iff]
  refine forall₂_congr fun C D ↦
    ⟨fun h ↦ subset_antisymm ?_ ?_, fun h P ↦ by rw [h, diamond_comp]⟩
  · exact diamond_le_diamond_iff.1 fun P ↦ (h P).le.trans (diamond_comp _ _ P).ge
  · exact diamond_le_diamond_iff.1 fun P ↦ (diamond_comp _ _ P).le.trans (h P).ge

end LinearOrder

end PointAlgebra
