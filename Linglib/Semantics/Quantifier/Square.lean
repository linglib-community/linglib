module

public import Linglib.Semantics.Quantifier.Basic
public import Linglib.Semantics.Quantifier.Negation

/-!
# The square of opposition of *every*, *no*, *some* and *not every*

For a restrictor `A`, the quantifiers `every A`, `no A`, `Det.some A` and `everyᶜ A` are the
corners of a square of opposition. It is the square of opposition of the quantifier `every A`,
whose corners are `every A`, its inner negation, its dual and its complement.

If `A` is empty then `every A` and `no A` both hold of every scope. So the relations of the
classical square of opposition hold if and only if `A` is nonempty, and `every A` and `no A` are
contrary if and only if `A` has at least two members.

## Main definitions

* `Quantifier.Det.square`: the square of opposition with corners `every A`, `no A`, `Det.some A`
  and `everyᶜ A`.

## Main results

* `Quantifier.Det.squareRelations_square`: the square at a restrictor `A` has the relations of
  the classical square of opposition if and only if `A` is nonempty.
* `Quantifier.Det.isContrary_every_no_iff`: `every A` and `no A` are contrary if and only if `A`
  has at least two members.

## Implementation notes

`Quantifier.Det.square A` has `Det.some A` as a corner, where the square of the quantifier
`every A` has the dual of `every A`. The two squares are equal, by `Quantifier.Det.square_eq`.
We keep both because `Det.some A` is the form that the consumers of the square use.

## References

* [peters-westerstahl-2006]
-/

@[expose] public section

namespace Quantifier.Det

variable {α : Type*} {A B : Set α}

/-- The square of opposition with corners `every A`, `no A`, `Det.some A` and `everyᶜ A`. -/
def square (A : Set α) : Aristotelian.Square (Quantifier α) where
  A := every A
  E := no A
  I := Det.some A
  O := (every : Det α)ᶜ A

theorem square_eq (A : Set α) : square A = (every A).square :=
  Aristotelian.Square.ext rfl rfl (congrFun dual_every A).symm rfl

/-- The square at a restrictor `A` has the relations of the classical square of opposition if
and only if `A` is nonempty. -/
theorem squareRelations_square : Aristotelian.SquareRelations (square A) ↔ A.Nonempty := by
  rw [square_eq, Quantifier.squareRelations_square_iff,
    le_dual_iff_not_apply_empty (monotone_every A) fun _ _ ↦ Set.subset_inter, every_apply_empty,
    Set.nonempty_iff_ne_empty]

theorem some_inf_compl_every_ne_bot_iff :
    Det.some A ⊓ (every : Det α)ᶜ A ≠ ⊥ ↔ A.Nontrivial := by
  rw [Function.ne_iff]
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨⟨x, hxA, hxB⟩, hne⟩ : Det.some A B ∧ ¬ every A B := by simpa using hB
    obtain ⟨y, hyA, hyB⟩ := Set.not_subset.1 hne
    exact ⟨x, hxA, y, hyA, fun h ↦ hyB (h ▸ hxB)⟩
  · rintro ⟨x, hx, y, hy, hne⟩
    have h : Det.some A {x} ∧ ¬ every A {x} := ⟨⟨x, hx, rfl⟩, fun h ↦ hne (h hy).symm⟩
    exact ⟨{x}, by simpa using h⟩

/-- `every A` and `no A` are contrary, that is, they cannot both hold and they can both fail,
if and only if `A` has at least two members. -/
theorem isContrary_every_no_iff : Aristotelian.IsContrary (every A) (no A) ↔ A.Nontrivial :=
  ⟨fun h ↦ some_inf_compl_every_ne_bot_iff.1 <|
      (squareRelations_square.2 (disjoint_every_no_iff.1 h.disjoint)).isContrary_AE_iff.1 h,
    fun h ↦ (squareRelations_square.2 h.nonempty).isContrary_AE_iff.2 <|
      some_inf_compl_every_ne_bot_iff.2 h⟩

end Quantifier.Det
