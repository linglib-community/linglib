module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Tactic.DeriveFintype

/-!
# The square of opposition

The square of opposition, in the form Horn surveys, has four corners `A`, `E`, `I`, `O` in a
Boolean algebra, related by contradiction (A–O, E–I), contrariety (A–E), subcontrariety (I–O)
and subalternation (A→I, E→O). Its instances for generalized quantifiers, after Barwise and
Cooper, and for modals live with those theories.

A square with these relations divides its algebra into three pairwise contrary parts, `E`, `A`,
and between them the conjunction `I ⊓ O` of the two particulars: the vertices of Horn's triangle
of opposition. Horn traces this trichotomy to De Morgan and to Jespersen's tripartition into
*all*, *some* and *none*, whose middle term is neither the I nor the O corner but their
conjunction; modally the vertices are the impossible, the contingent and the necessary. Ordered
by the affirmative corners they lie in, the vertices form the scale *none* < *some but not all* <
*all*.

## Main definitions

* `Square`, `SquareRelations`: a square and the relations of the square.
* `Triangle`, `Square.triangle`: the vertices of the triangle of opposition and the element of a
  square at each.
* `Triangle.corners`: the corners of the square as sets of vertices, and the order of the
  vertices by the affirmative corners they lie in.

## Main results

* `SquareRelations.subalternAI`, `SquareRelations.subalternEO`, `SquareRelations.subcontrIO`:
  the remaining relations of the square.
* `SquareRelations.pairwise_disjoint_triangle`, `SquareRelations.sup_triangle`: the vertices of
  a square are pairwise disjoint and join to `⊤`.
* `Triangle.squareRelations_corners`, `Triangle.triangle_corners`: the corners as sets of
  vertices satisfy the relations, and the vertices are the singletons.
* `Triangle.mem_corners_I`, `Triangle.mem_corners_A`: *some* holds above the bottom vertex and
  *all* at the top one.

## References

* [barwise-cooper-1981]
* [horn-2001]
-/

@[expose] public section

namespace Aristotelian

/-! ### The square -/

/-- A square of opposition has four corners. -/
structure Square (α : Type*) where
  /-- `A` is the universal affirmative corner (*every*, `□p`, `Bel p`). -/
  A : α
  /-- `E` is the universal negative corner (*no*, `□¬p`, `Bel ¬p`). -/
  E : α
  /-- `I` is the particular affirmative corner (*some*, `◇p`). -/
  I : α
  /-- `O` is the particular negative corner (*not every*, `¬□p`, `¬Bel p`). -/
  O : α

/-- The vertices of the triangle of opposition, in scale order, are the universal negative `E`,
the conjunction `IO` of the two particulars, and the universal affirmative `A`. -/
inductive Triangle where
  | E
  | IO
  | A
  deriving DecidableEq, Repr, Fintype

/-- The element of a square at a vertex of its triangle. -/
def Square.triangle {α : Type*} [BooleanAlgebra α] (sq : Square α) : Triangle → α
  | .E => sq.E
  | .IO => sq.I ⊓ sq.O
  | .A => sq.A

namespace Triangle

/-- The corners of the square, each given as the set of vertices at which it holds. -/
def corners : Square (Finset Triangle) := ⟨{.A}, {.E}, {.IO, .A}, {.E, .IO}⟩

/-- The element of `corners` at each vertex is that vertex's singleton. -/
theorem triangle_corners (t : Triangle) : corners.triangle t = {t} := by
  cases t <;> decide

/-- A vertex lies below another when the other lies in every affirmative corner that it does. -/
instance : LE Triangle :=
  ⟨fun s t ↦ (s ∈ corners.I → t ∈ corners.I) ∧ (s ∈ corners.A → t ∈ corners.A)⟩

instance : DecidableLE Triangle := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : LinearOrder Triangle where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  toDecidableLE := inferInstance

instance : BoundedOrder Triangle where
  top := .A
  le_top := by decide
  bot := .E
  bot_le := by decide

theorem bot_eq_E : (⊥ : Triangle) = .E := rfl

theorem top_eq_A : (⊤ : Triangle) = .A := rfl

/-- *Some* holds above the bottom vertex. -/
theorem mem_corners_I {t : Triangle} : t ∈ corners.I ↔ ⊥ < t := by decide +revert

/-- *All* holds at the top vertex. -/
theorem mem_corners_A {t : Triangle} : t ∈ corners.A ↔ t = ⊤ := by decide +revert

theorem mem_corners_O {t : Triangle} : t ∈ corners.O ↔ t < ⊤ := by decide +revert

theorem mem_corners_E {t : Triangle} : t ∈ corners.E ↔ t = ⊥ := by decide +revert

end Triangle

/-! ### Square relations -/

variable {α : Type*} [BooleanAlgebra α] {sq : Square α}

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

theorem of_disjoint (hI : sq.I = sq.Eᶜ) (hO : sq.O = sq.Aᶜ) (h : Disjoint sq.A sq.E) :
    SquareRelations sq :=
  ⟨hO ▸ isCompl_compl, hI ▸ isCompl_compl, h⟩

/-! ### The cells -/

theorem inf_IO_eq (h : SquareRelations sq) : sq.I ⊓ sq.O = (sq.A ⊔ sq.E)ᶜ := by
  rw [h.contradEI.symm.eq_compl, h.contradAO.symm.eq_compl, compl_sup, inf_comm]

open Function in
/-- The vertices of a square are pairwise disjoint. -/
theorem pairwise_disjoint_triangle (h : SquareRelations sq) :
    Pairwise (Disjoint on sq.triangle) := by
  have hA : Disjoint sq.A (sq.I ⊓ sq.O) := by
    rw [h.inf_IO_eq]; exact disjoint_compl_right.mono_right (compl_le_compl le_sup_left)
  have hE : Disjoint sq.E (sq.I ⊓ sq.O) := by
    rw [h.inf_IO_eq]; exact disjoint_compl_right.mono_right (compl_le_compl le_sup_right)
  rintro (_ | _ | _) (_ | _ | _) hne <;> first
    | exact absurd rfl hne
    | simp only [onFun, Square.triangle]
  exacts [hE, h.contraryAE.symm, hE.symm, hA.symm, h.contraryAE, hA]

/-- The vertices of a square join to `⊤`. -/
theorem sup_triangle (h : SquareRelations sq) :
    sq.triangle .E ⊔ sq.triangle .IO ⊔ sq.triangle .A = ⊤ := by
  simp only [Square.triangle]
  rw [h.inf_IO_eq]
  calc sq.E ⊔ (sq.A ⊔ sq.E)ᶜ ⊔ sq.A = (sq.A ⊔ sq.E)ᶜ ⊔ (sq.A ⊔ sq.E) := by ac_rfl
    _ = ⊤ := compl_sup_eq_top

end SquareRelations

/-- The corners as sets of vertices satisfy the relations of the square. -/
theorem Triangle.squareRelations_corners : SquareRelations Triangle.corners :=
  .of_disjoint (by decide) (by decide) (by decide)

end Aristotelian
