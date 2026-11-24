module

public import Linglib.Core.Algebra.Ring.BooleanRing
public import Linglib.Semantics.Quantifier.Defs
public import Linglib.Logic.Aristotelian.Square
public import Linglib.Semantics.Negation.Polarity
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# The negations of a quantifier

A quantifier `Q` can be negated in two places. Outer negation negates the value: it is the
complement `Qᶜ`. Inner negation negates the scope: `Q.innerNeg B = Q Bᶜ`. Doing both gives the
dual, `Q.dual B = ¬ Q Bᶜ`.

A quantifier with its inner negation, its dual and its complement forms a square of opposition.
The diagonals of the square are contradictory for every quantifier, and its other classical
relations hold if and only if `Q ≤ Q.dual`.

The two negations are the two ways a group acting on truth values and on sets acts on the functions
from sets to truth values. The polarities act on truth values by negation, and so on a quantifier
through its value; they act on sets by complement, and so on a quantifier through its scope, which
is the action of `DomMulAct Polarity`. The two actions commute. Together they are an action of the
pairs of an outer and an inner polarity, and the orbit of a quantifier is its square. A monotone or
antitone quantifier stays monotone or antitone under each action, and the direction changes once for
each negative polarity.

## Main definitions

* `Quantifier.square`: the square of opposition of a quantifier `Q`, with corners `Q`,
  `Q.innerNeg`, `Q.dual` and `Qᶜ`.

## Main results

* `Quantifier.squareRelations_square_iff`: the square of `Q` has the relations of the classical
  square of opposition if and only if `Q ≤ Q.dual`.
* `Quantifier.negative_smul`, `Quantifier.mk_negative_smul`: the negative polarity acts on a
  quantifier through the value as the complement and through the scope as inner negation.
* `Quantifier.orbit_eq`: the orbit of `Q` under the two actions is `Q`, `Q.innerNeg`, `Q.dual`
  and `Qᶜ`.
* `Polarity.MonoBy.smul`, `Polarity.MonoBy.mk_smul`: a polarity acting on a quantifier through
  either place multiplies its direction by that polarity.
* `Quantifier.mk_toBoolRing_univ_vadd`: a set acts on a quantifier by complementing the scope
  within that set, and inner negation is the action of the whole universe.

## Implementation notes

The action through the scope is mathlib's action of `DomMulAct M` on a function type whose domain
`M` acts on, here with the polarities acting on sets by complement. That it is an action, and that
it commutes with the action through the value, are instances of that file. A homomorphism from
pairs of polarities into the functions from quantifiers to quantifiers would say the same and
provide none of the lemmas about actions, such as that every point of an orbit has that orbit,
`MulAction.orbit_smul`.

## References

* [peters-westerstahl-2006]
-/

@[expose] public section

namespace Quantifier

variable {α : Type*} {Q : Quantifier α}

/-! ### The square of opposition of a quantifier

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

/-! ### The action of the polarities -/

open DomMulAct

@[simp] theorem negative_smul (Q : Quantifier α) : Polarity.negative • Q = Qᶜ := rfl

@[simp] theorem mk_negative_smul (Q : Quantifier α) : mk Polarity.negative • Q = Q.innerNeg := rfl

theorem negative_smul_mk_negative_smul (Q : Quantifier α) :
    Polarity.negative • mk Polarity.negative • Q = Q.dual := rfl

/-- The pairs of an outer and an inner polarity act on quantifiers, the outer one through the
value and the inner one through the scope. -/
instance : MulAction (Polarity × DomMulAct Polarity) (Quantifier α) :=
  MulAction.prodOfSMulCommClass _ _ _

/-- The orbit of a quantifier under the two actions of the polarities is its square of
opposition. -/
theorem orbit_eq (Q : Quantifier α) :
    MulAction.orbit (Polarity × DomMulAct Polarity) Q = {Q, Q.innerNeg, Q.dual, Qᶜ} := by
  ext Q'
  simp only [MulAction.mem_orbit_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨o, i⟩, rfl⟩
    obtain ⟨i, rfl⟩ := mk.surjective i
    cases o <;> cases i
    exacts [.inl rfl, .inr (.inl rfl), .inr (.inr (.inr rfl)), .inr (.inr (.inl rfl))]
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨1, one_smul _ _⟩, ⟨(.positive, mk .negative), rfl⟩,
      ⟨(.negative, mk .negative), rfl⟩, ⟨(.negative, mk .positive), rfl⟩]

/-! ### Flipping part of the scope

Inner negation complements the whole scope. A set `N` of individuals acts on a quantifier by
complementing the scope within `N` only, taking `Q` to the quantifier that holds of `B` when `Q`
holds of `N ∆ B`. These are the actions of the sets under symmetric difference, and inner negation
is the action of the whole universe. -/

theorem mk_toBoolRing_vadd_apply (N B : Set α) (Q : Quantifier α) :
    (DomAddAct.mk (toBoolRing N) +ᵥ Q) B = Q (symmDiff N B) := rfl

/-- Inner negation is the flip of the whole scope. -/
theorem mk_toBoolRing_univ_vadd (Q : Quantifier α) :
    DomAddAct.mk (toBoolRing (Set.univ : Set α)) +ᵥ Q = Q.innerNeg :=
  funext fun B ↦ congrArg Q (AsBoolRing.toBoolRing_top_vadd B)

end Quantifier

namespace Polarity.MonoBy

open Quantifier DomMulAct

variable {α : Type*} {Q : Quantifier α} {s : Polarity}

/-- If `Q` is directed by `s`, then `o • Q` is directed by `o * s`. -/
protected theorem smul (h : s.MonoBy Q) (o : Polarity) : (o * s).MonoBy (o • Q) := by
  cases o
  · exact h
  · cases s
    exacts [fun _ _ hB hn hq ↦ hn (h hB hq), fun _ _ hB hn hq ↦ hn (h hB hq)]

/-- If `Q` is directed by `s`, then `mk i • Q` is directed by `i * s`. -/
protected theorem mk_smul (h : s.MonoBy Q) (i : Polarity) : (i * s).MonoBy (mk i • Q) := by
  cases i
  · exact h
  · cases s
    exacts [fun _ _ hB ↦ h (Set.compl_subset_compl.2 hB),
      fun _ _ hB ↦ h (Set.compl_subset_compl.2 hB)]

/-- If `Q` is directed by `s`, then `o • mk i • Q` is directed by `o * i * s`. In particular the
dual of a monotone quantifier is monotone. -/
protected theorem smul_mk_smul (h : s.MonoBy Q) (o i : Polarity) :
    (o * i * s).MonoBy (o • mk i • Q) := by
  rw [mul_assoc]
  exact (h.mk_smul i).smul o

end Polarity.MonoBy
