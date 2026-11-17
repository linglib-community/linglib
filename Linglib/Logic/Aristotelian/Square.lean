module

public import Linglib.Logic.Aristotelian.Basic
public import Mathlib.Order.Hom.BoundedLattice

/-!
# The square of opposition

The square of opposition, in the form Horn surveys, has four corners `A`, `E`, `I`, `O` in a
Boolean algebra, with contradictory diagonals and universals `A`, `E` that cannot both hold. A
square with these relations is [determined by its two universals](##squareRelations_iff), and in
it [`A` entails `I`](##SquareRelations.subalternAI), [`E` entails
`O`](##SquareRelations.subalternEO), and [`I` and `O` cannot both
fail](##SquareRelations.subcontrIO). Its instances for generalized quantifiers and for modals
live with those theories.

Between the universals lies the conjunction `I ⊓ O` of the two particulars, Jespersen's *some
but not all* and the modal contingent, which is [what `A` and `E` leave
uncovered](##SquareRelations.inf_IO_eq). It decides how much of the square is left: `A` and `E`
are [contrary](##SquareRelations.isContrary_AE_iff), `I` and `O`
[subcontrary](##SquareRelations.isSubcontrary_IO_iff) and the two entailments
[strict](##SquareRelations.lt_AI_iff) exactly when it is not `⊥`.

## Implementation notes

`SquareRelations` asks only that `A` and `E` be disjoint, where Horn's contraries may also both
fail; that half is `I ⊓ O ≠ ⊥` and is left to the theorems that need it, so that a square whose
restrictor has one member, or whose modal base settles the prejacent, is still a square.

## References

* [horn-2001]
-/

@[expose] public section

namespace Aristotelian

variable {F α β γ : Type*}

/-! ### The square -/

/-- A square of opposition has four corners. -/
@[ext]
structure Square (α : Type*) where
  /-- `A` is the universal affirmative corner (*every*, `□p`, `Bel p`). -/
  A : α
  /-- `E` is the universal negative corner (*no*, `□¬p`, `Bel ¬p`). -/
  E : α
  /-- `I` is the particular affirmative corner (*some*, `◇p`). -/
  I : α
  /-- `O` is the particular negative corner (*not every*, `¬□p`, `¬Bel p`). -/
  O : α

namespace Square

/-- The image of a square under a map of its corners. -/
@[simps]
def map (f : α → β) (sq : Square α) : Square β := ⟨f sq.A, f sq.E, f sq.I, f sq.O⟩

@[simp] theorem map_id (sq : Square α) : sq.map id = sq := rfl

@[simp] theorem map_map (g : β → γ) (f : α → β) (sq : Square α) :
    (sq.map f).map g = sq.map (g ∘ f) := rfl

/-- The inner negation of a square negates what its corners quantify over, exchanging `A` with `E`
and `I` with `O`: *not every* is *some* over the negated scope. -/
@[simps]
def inner (sq : Square α) : Square α := ⟨sq.E, sq.A, sq.O, sq.I⟩

@[simp] theorem inner_inner (sq : Square α) : sq.inner.inner = sq := rfl

theorem map_inner (f : α → β) (sq : Square α) : sq.inner.map f = (sq.map f).inner := rfl

/-- The square on two universals has their complements for particulars. -/
@[simps]
def ofUniversals [Compl α] (a e : α) : Square α := ⟨a, e, eᶜ, aᶜ⟩

end Square

/-! ### Square relations -/

variable [BooleanAlgebra α] {sq : Square α}

/-- A square over a Boolean algebra satisfies the relations of the square when both diagonals
are contradictory and the universals cannot both hold. Subalternation and subcontrariety follow
(`subalternAI`, `subalternEO`, `subcontrIO`). -/
structure SquareRelations (sq : Square α) : Prop where
  /-- `A` and `O` are contradictories. -/
  contradAO : IsCompl sq.A sq.O
  /-- `E` and `I` are contradictories. -/
  contradEI : IsCompl sq.E sq.I
  /-- `A` and `E` cannot both hold. -/
  contraryAE : Disjoint sq.A sq.E

namespace SquareRelations

theorem of_disjoint (hI : sq.I = sq.Eᶜ) (hO : sq.O = sq.Aᶜ) (h : Disjoint sq.A sq.E) :
    SquareRelations sq :=
  ⟨hO ▸ isCompl_compl, hI ▸ isCompl_compl, h⟩

/-- A square with the relations is the square on its universals. -/
theorem eq_ofUniversals (h : SquareRelations sq) : sq = .ofUniversals sq.A sq.E :=
  Square.ext rfl rfl h.contradEI.compl_eq.symm h.contradAO.compl_eq.symm

/-- `A` entails `I`. -/
theorem subalternAI (h : SquareRelations sq) : sq.A ≤ sq.I := by
  rw [h.contradEI.symm.eq_compl]
  exact le_compl_iff_disjoint_right.mpr h.contraryAE

/-- `E` entails `O`. -/
theorem subalternEO (h : SquareRelations sq) : sq.E ≤ sq.O := by
  rw [h.contradAO.symm.eq_compl]
  exact le_compl_iff_disjoint_right.mpr h.contraryAE.symm

/-- `I` and `O` cannot both fail. -/
theorem subcontrIO (h : SquareRelations sq) : Codisjoint sq.I sq.O := by
  rw [h.contradEI.symm.eq_compl, h.contradAO.symm.eq_compl, codisjoint_iff, ← compl_inf,
    disjoint_iff.mp h.contraryAE.symm, compl_bot]

/-- The relations of the square survive inner negation. -/
protected theorem inner (h : SquareRelations sq) : SquareRelations sq.inner :=
  ⟨h.contradEI, h.contradAO, h.contraryAE.symm⟩

/-- A bounded lattice homomorphism carries a square with the relations to one. -/
protected theorem map [BooleanAlgebra β] [FunLike F α β] [BoundedLatticeHomClass F α β]
    (h : SquareRelations sq) (f : F) : SquareRelations (sq.map f) :=
  ⟨h.contradAO.map f, h.contradEI.map f, h.contraryAE.map f⟩

end SquareRelations

/-- The square on two universals satisfies the relations exactly when they cannot both hold. -/
@[simp] theorem squareRelations_ofUniversals {a e : α} :
    SquareRelations (.ofUniversals a e) ↔ Disjoint a e :=
  ⟨fun h ↦ h.contraryAE, fun h ↦ .of_disjoint rfl rfl h⟩

/-- A square satisfies the relations exactly when it is the square on two universals that cannot
both hold. -/
theorem squareRelations_iff :
    SquareRelations sq ↔ Disjoint sq.A sq.E ∧ sq = .ofUniversals sq.A sq.E :=
  ⟨fun h ↦ ⟨h.contraryAE, h.eq_ofUniversals⟩,
    fun ⟨h, hsq⟩ ↦ hsq ▸ squareRelations_ofUniversals.2 h⟩

/-! ### The middle vertex -/

namespace SquareRelations

theorem inf_IO_eq (h : SquareRelations sq) : sq.I ⊓ sq.O = (sq.A ⊔ sq.E)ᶜ := by
  rw [h.contradEI.symm.eq_compl, h.contradAO.symm.eq_compl, compl_sup, inf_comm]

theorem I_sdiff_O (h : SquareRelations sq) : sq.I \ sq.O = sq.A := by
  rw [sdiff_eq, ← h.contradAO.eq_compl, inf_eq_right.2 h.subalternAI]

theorem I_sdiff_A (h : SquareRelations sq) : sq.I \ sq.A = sq.I ⊓ sq.O := by
  rw [sdiff_eq, h.contradAO.compl_eq]

theorem inf_IO_sup_A (h : SquareRelations sq) : sq.I ⊓ sq.O ⊔ sq.A = sq.I := by
  rw [← h.I_sdiff_A, sdiff_sup_cancel h.subalternAI]

theorem inf_IO_sup_E (h : SquareRelations sq) : sq.I ⊓ sq.O ⊔ sq.E = sq.O := by
  rw [inf_comm]
  exact h.inner.inf_IO_sup_A

/-- `A` entails `I` strictly exactly when the two particulars can hold together. -/
theorem lt_AI_iff (h : SquareRelations sq) : sq.A < sq.I ↔ sq.I ⊓ sq.O ≠ ⊥ := by
  rw [lt_iff_le_not_ge, and_iff_right h.subalternAI, ne_eq, ← disjoint_iff,
    ← le_compl_iff_disjoint_right, h.contradAO.symm.compl_eq]

/-- `E` entails `O` strictly exactly when the two particulars can hold together. -/
theorem lt_EO_iff (h : SquareRelations sq) : sq.E < sq.O ↔ sq.I ⊓ sq.O ≠ ⊥ := by
  rw [inf_comm]
  exact h.inner.lt_AI_iff

/-- The universals are contrary, able both to fail, exactly when the two particulars can hold
together. -/
theorem isContrary_AE_iff (h : SquareRelations sq) :
    IsContrary sq.A sq.E ↔ sq.I ⊓ sq.O ≠ ⊥ := by
  rw [isContrary_iff_lt_compl, h.contradEI.compl_eq, h.lt_AI_iff]

/-- The particulars are subcontrary exactly when they can hold together. -/
theorem isSubcontrary_IO_iff (h : SquareRelations sq) :
    IsSubcontrary sq.I sq.O ↔ sq.I ⊓ sq.O ≠ ⊥ := by
  rw [isSubcontrary_iff, and_iff_right h.subcontrIO, disjoint_iff]

end SquareRelations

end Aristotelian
