module

public import Linglib.Logic.Aristotelian.Square
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Tactic.DeriveFintype

/-!
# The triangle of opposition

A square of opposition divides its algebra into three parts, `E`, `A`, and between them the
conjunction of the two particulars: the vertices of Horn's triangle of opposition. Horn traces
this trichotomy to De Morgan and to Jespersen's tripartition into *all*, *some* and *none*, whose
middle term is neither the `I` nor the `O` corner but their conjunction; modally the vertices are
the impossible, the contingent and the necessary.

`Triangle` is the type of the three vertices, and serves as the state space of a scalar item
with its stronger alternative. Each corner of the square is the set of vertices at which it
holds, and these four sets [form a square](##Aristotelian.Triangle.squareRelations_corners) in
`Finset Triangle`. The vertices are ordered by the affirmative corners they lie in, which is the
scale *none* < *some but not all* < *all*: *some* holds [above the bottom
vertex](##Aristotelian.Triangle.mem_corners_I) and *all* [at the
top](##Aristotelian.Triangle.mem_corners_A).

## References

* [horn-2001]
-/

@[expose] public section

namespace Aristotelian

/-- The vertices of the triangle of opposition, in scale order. -/
inductive Triangle where
  /-- *None*, the universal negative `E`. -/
  | none
  /-- *Some but not all*, the conjunction of the two particulars `I` and `O`. -/
  | someNotAll
  /-- *All*, the universal affirmative `A`. -/
  | all
  deriving DecidableEq, Repr, Fintype

namespace Triangle

theorem univ_eq : (Finset.univ : Finset Triangle) = {.none, .someNotAll, .all} := rfl

/-- The corners of the square, each given as the set of vertices at which it holds. -/
def corners : Square (Finset Triangle) :=
  ⟨{.all}, {.none}, {.someNotAll, .all}, {.none, .someNotAll}⟩

/-- The corners as sets of vertices satisfy the relations of the square. -/
theorem squareRelations_corners : SquareRelations corners :=
  .of_disjoint (by decide) (by decide) (by decide)

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
  top := .all
  le_top := by decide
  bot := .none
  bot_le := by decide

theorem bot_eq_none : (⊥ : Triangle) = .none := rfl

theorem top_eq_all : (⊤ : Triangle) = .all := rfl

/-- *Some* holds above the bottom vertex. -/
theorem mem_corners_I {t : Triangle} : t ∈ corners.I ↔ ⊥ < t := by decide +revert

/-- *All* holds at the top vertex. -/
theorem mem_corners_A {t : Triangle} : t ∈ corners.A ↔ t = ⊤ := by decide +revert

theorem mem_corners_O {t : Triangle} : t ∈ corners.O ↔ t < ⊤ := by decide +revert

theorem mem_corners_E {t : Triangle} : t ∈ corners.E ↔ t = ⊥ := by decide +revert

end Triangle

end Aristotelian
