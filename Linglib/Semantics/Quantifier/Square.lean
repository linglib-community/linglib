module

public import Linglib.Semantics.Quantifier.Basic
public import Linglib.Logic.Aristotelian.Square

/-!
# The square of opposition of a quantifier

A quantifier `Q` with its inner negation, its dual and its complement forms a square of
opposition, with `Q` and `Q.innerNeg` as the universal corners. Its diagonals are contradictory
for every `Q`, and its other classical relations hold if and only if `Q` and `Q.innerNeg` cannot
both hold, that is, if and only if `Q ≤ Q.dual`.

For a restrictor `A`, the square of `every A` has the corners `every A`, `no A`, `Det.some A` and
`everyᶜ A`. If `A` is empty then `every A` and `no A` both hold of every scope. So the classical
relations hold if and only if `A` is nonempty, and `every A` and `no A` are contrary if and only
if `A` has at least two members.

## Main results

* `Quantifier.squareRelations_square_iff`: the square of `Q` has the relations of the classical
  square of opposition if and only if `Q ≤ Q.dual`.
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

namespace Quantifier

variable {α : Type*} {Q : Quantifier α}

/-! ### The square of a quantifier

The square of opposition of a quantifier `Q` has the corners `Q`, `Q.innerNeg`, `Q.dual` and
`Qᶜ`. In every such square the diagonals are contradictory. The other relations of the classical
square say that the two universal corners `Q` and `Q.innerNeg` cannot both hold; this is the
case if and only if `Q ≤ Q.dual`. -/

/-- The square of opposition of a quantifier `Q`, with corners `Q`, `Q.innerNeg`, `Q.dual` and
`Qᶜ` ([peters-westerstahl-2006]). -/
@[simps]
def square (Q : Quantifier α) : Aristotelian.Square (Quantifier α) := ⟨Q, Q.innerNeg, Q.dual, Qᶜ⟩

theorem square_eq_ofUniversals (Q : Quantifier α) : Q.square = .ofUniversals Q Q.innerNeg := rfl

/-- The square of `Q.innerNeg` is the square of `Q` with the two universal corners exchanged
and the two particular corners exchanged. -/
theorem square_innerNeg (Q : Quantifier α) : Q.innerNeg.square = Q.square.inner :=
  Aristotelian.Square.ext rfl (innerNeg_innerNeg Q) (congrArg (·ᶜ) (innerNeg_innerNeg Q)) rfl

theorem disjoint_innerNeg_iff : Disjoint Q Q.innerNeg ↔ Q ≤ Q.dual :=
  le_compl_iff_disjoint_right.symm

/-- The square of `Q` has the relations of the classical square of opposition if and only if
`Q ≤ Q.dual`. -/
theorem squareRelations_square_iff : Aristotelian.SquareRelations Q.square ↔ Q ≤ Q.dual :=
  Aristotelian.squareRelations_ofUniversals.trans disjoint_innerNeg_iff

/-- If `Q` is monotone and closed under intersections of scopes, then `Q ≤ Q.dual` if and only
if `Q` does not hold of the empty set. -/
theorem le_dual_iff_not_apply_empty (hm : Monotone Q) (hi : ∀ B C, Q B → Q C → Q (B ∩ C)) :
    Q ≤ Q.dual ↔ ¬ Q ∅ :=
  ⟨fun h h₀ ↦ h ∅ h₀ (hm (Set.empty_subset _) h₀),
    fun h B hB hB' ↦ h (Set.inter_compl_self B ▸ hi _ _ hB hB')⟩

end Quantifier

/-! ### The square of *every*, *no*, *some* and *not every* -/

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
