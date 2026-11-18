module

public import Linglib.Logic.Temporal.PointAlgebra
public import Linglib.Semantics.Denotation
public import Linglib.Syntax.Category.Verb.Tense

/-!
# Grammatical tense

A tense, past, present or future (`Tense`, from `Syntax/Category/Verb/Tense.lean`), denotes an
element of the point algebra (`PointAlgebra`), the orderings in which a reference time may stand
to a perspective time, so the constraint a tense imposes on times `r` and `p` is
`compare r p ∈ ⟦t⟧`. Following Kiparsky, tense locates the reference time relative to the
perspective time, not the speech time. The derived categories are joins and complements of tense
denotations rather than further tenses: Klecha's [nonpast](##Tense.nonpast) is
`⟦present⟧ ⊔ ⟦future⟧`, the [nonfuture](##Tense.nonfuture) is `⟦past⟧ ⊔ ⟦present⟧`, and the
unconstrained element is `⊤`. A tense under a tense denotes the product of the two.

## References

* [kiparsky-2002]
* [klecha-2016]
-/

@[expose] public section

namespace Tense

open PointAlgebra SetRel
open scoped Denotes

/-- A tense denotes the orderings in which the reference time may stand to the perspective time,
before it for the past, at it for the present and after it for the future. -/
def denote : Tense → PointAlgebra
  | past => {.lt}
  | present => 1
  | future => {.gt}

instance : Denotes Tense PointAlgebra := ⟨denote⟩

theorem denote_past : ⟦past⟧ = ({.lt} : PointAlgebra) := rfl

theorem denote_present : ⟦present⟧ = (1 : PointAlgebra) := rfl

theorem denote_future : ⟦future⟧ = ({.gt} : PointAlgebra) := rfl

theorem mem_past {o : Ordering} : o ∈ ⟦past⟧ ↔ o = .lt := mem_singleton

theorem mem_present {o : Ordering} : o ∈ ⟦present⟧ ↔ o = .eq := mem_one

theorem mem_future {o : Ordering} : o ∈ ⟦future⟧ ↔ o = .gt := mem_singleton

@[simp] theorem inv_past : (⟦past⟧ : PointAlgebra)⁻¹ = ⟦future⟧ := by decide

@[simp] theorem inv_future : (⟦future⟧ : PointAlgebra)⁻¹ = ⟦past⟧ := by decide

@[simp] theorem past_mul_past : (⟦past⟧ : PointAlgebra) * ⟦past⟧ = ⟦past⟧ := by decide

@[simp] theorem future_mul_future : (⟦future⟧ : PointAlgebra) * ⟦future⟧ = ⟦future⟧ := by decide

@[simp] theorem past_mul_future : (⟦past⟧ : PointAlgebra) * ⟦future⟧ = ⊤ := by decide

@[simp] theorem future_mul_past : (⟦future⟧ : PointAlgebra) * ⟦past⟧ = ⊤ := by decide

/-- The nonpast is a reference time at or after the perspective time. -/
def nonpast : PointAlgebra := {.eq, .gt}

theorem nonpast_eq_present_sup_future : nonpast = ⟦present⟧ ⊔ ⟦future⟧ := by decide

theorem nonpast_eq_compl_past : nonpast = ⟦past⟧ᶜ := by decide

/-- The nonfuture is a reference time before or at the perspective time. -/
def nonfuture : PointAlgebra := {.lt, .eq}

theorem nonfuture_eq_past_sup_present : nonfuture = ⟦past⟧ ⊔ ⟦present⟧ := by decide

theorem nonfuture_eq_compl_future : nonfuture = ⟦future⟧ᶜ := by decide

theorem past_le_nonfuture : ⟦past⟧ ≤ nonfuture := by decide

theorem one_le_nonfuture : 1 ≤ nonfuture := by decide

@[simp] theorem nonfuture_mul_nonfuture : nonfuture * nonfuture = nonfuture := by decide

variable {T : Type*} {p r : T}

/-! ### The relations of the tenses -/

section LT

variable [LT T]

@[simp] theorem mem_toSetRel_past : p ~[toSetRel ⟦past⟧] r ↔ r < p := mem_toSetRel_lt

@[simp] theorem mem_toSetRel_present : p ~[toSetRel ⟦present⟧] r ↔ r = p := mem_toSetRel_one

@[simp] theorem mem_toSetRel_future : p ~[toSetRel ⟦future⟧] r ↔ p < r := mem_toSetRel_gt

@[simp] theorem inv_toSetRel_past : (toSetRel ⟦past⟧ : SetRel T T).inv = toSetRel ⟦future⟧ := by
  rw [← toSetRel_inv, inv_past]

@[simp] theorem inv_toSetRel_future : (toSetRel ⟦future⟧ : SetRel T T).inv = toSetRel ⟦past⟧ := by
  rw [← toSetRel_inv, inv_future]

end LT

theorem mem_toSetRel_nonfuture [PartialOrder T] : p ~[toSetRel nonfuture] r ↔ r ≤ p := by
  simp [mem_toSetRel, nonfuture, le_iff_lt_or_eq]

instance [Preorder T] : (toSetRel ⟦past⟧ : SetRel T T).IsTrans :=
  inferInstanceAs (toSetRel {.lt} : SetRel T T).IsTrans

instance [Preorder T] : (toSetRel ⟦future⟧ : SetRel T T).IsTrans :=
  inferInstanceAs (toSetRel {.gt} : SetRel T T).IsTrans

section LinearOrder

variable [LinearOrder T]

@[simp] theorem compare_mem_past (r p : T) : compare r p ∈ ⟦past⟧ ↔ r < p := by
  rw [mem_past, compare_lt_iff_lt]

@[simp] theorem compare_mem_present (r p : T) : compare r p ∈ ⟦present⟧ ↔ r = p := by
  rw [mem_present, compare_eq_iff_eq]

@[simp] theorem compare_mem_future (r p : T) : compare r p ∈ ⟦future⟧ ↔ p < r := by
  rw [mem_future, compare_gt_iff_gt]

@[simp] theorem compare_mem_nonpast (r p : T) : compare r p ∈ nonpast ↔ p ≤ r := by
  rw [nonpast_eq_compl_past, mem_compl, compare_mem_past, not_lt]

@[simp] theorem compare_mem_nonfuture (r p : T) : compare r p ∈ nonfuture ↔ r ≤ p := by
  rw [nonfuture_eq_compl_future, mem_compl, compare_mem_future, not_lt]

end LinearOrder

end Tense
