module

public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Negation.Polarity
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The negations of a quantifier as an action of the polarities

A quantifier `Q` can be negated in two places. Outer negation negates the value: it is the
complement `Qᶜ`. Inner negation negates the scope: `Q.innerNeg B = Q Bᶜ`. Doing both gives the
dual, `Q.dual B = ¬ Q Bᶜ`.

This file defines the map `Quantifier.negHom` that sends a pair `(o, i)` of polarities to the
operation that negates the value if `o` is negative and the scope if `i` is negative. It is a
homomorphism from the group `Polarity × Polarity` to the functions from quantifiers to
quantifiers, since the two negations commute and each is its own inverse.

The images of a quantifier `Q` under these four operations are the corners of the square of
opposition of `Q`. A monotone or antitone quantifier stays monotone or antitone under each of
the operations, and the direction changes once for each negative polarity in the pair.

## Main definitions

* `Quantifier.innerNegHom`: the homomorphism that sends the negative polarity to inner negation.
* `Quantifier.negHom`: the homomorphism that sends `(o, i)` to outer negation if `o` is
  negative, composed with inner negation if `i` is negative.

## Main results

* `Quantifier.range_negHom`: the images of `Q` under `negHom` are `Q`, `Q.innerNeg`, `Q.dual`
  and `Qᶜ`.
* `Quantifier.range_negHom_negHom`: each of these four quantifiers has the same four images, so
  each corner of a square of opposition has that same square.
* `Polarity.MonoBy.negHom`: if `Q` is monotone or antitone, as given by a polarity `s`, then
  `negHom (o, i) Q` is monotone or antitone as given by `o * i * s`.

## Implementation notes

We define a homomorphism into `Function.End (Quantifier α)` and not a `MulAction` instance.
`Quantifier α` is an abbreviation of the function type `Set α → Prop`, so an instance on it would
apply to every function from sets to propositions.

## References

* [peters-westerstahl-2006]
-/

@[expose] public section

namespace Quantifier

variable {α : Type*} {Q : Quantifier α}

/-- The homomorphism from the polarities to the operations on quantifiers that sends the negative
polarity to inner negation. -/
def innerNegHom : Polarity →* Function.End (Quantifier α) :=
  Polarity.lift ⟨innerNeg, (show Function.Involutive innerNeg from innerNeg_innerNeg).comp_self⟩

@[simp] theorem innerNegHom_positive (Q : Quantifier α) : innerNegHom .positive Q = Q := rfl

@[simp] theorem innerNegHom_negative (Q : Quantifier α) : innerNegHom .negative Q = Q.innerNeg :=
  rfl

/-- The homomorphism that sends a pair `(o, i)` of polarities to the operation on quantifiers
that takes the complement if `o` is negative and the inner negation if `i` is negative. -/
def negHom : Polarity × Polarity →* Function.End (Quantifier α) :=
  Polarity.complHom.noncommCoprod innerNegHom fun o i ↦ by cases o <;> cases i <;> rfl

theorem negHom_apply (o i : Polarity) (Q : Quantifier α) :
    negHom (o, i) Q = Polarity.complHom o (innerNegHom i Q) := rfl

@[simp] theorem negHom_positive_positive (Q : Quantifier α) :
    negHom (.positive, .positive) Q = Q := rfl

@[simp] theorem negHom_negative_positive (Q : Quantifier α) :
    negHom (.negative, .positive) Q = Qᶜ := rfl

@[simp] theorem negHom_positive_negative (Q : Quantifier α) :
    negHom (.positive, .negative) Q = Q.innerNeg := rfl

@[simp] theorem negHom_negative_negative (Q : Quantifier α) :
    negHom (.negative, .negative) Q = Q.dual := rfl

theorem negHom_mul_apply (p q : Polarity × Polarity) (Q : Quantifier α) :
    negHom (p * q) Q = negHom p (negHom q Q) := by
  rw [map_mul]; rfl

/-- The images of `Q` under `negHom` are `Q`, `Q.innerNeg`, `Q.dual` and `Qᶜ`, the corners of the
square of opposition of `Q`. -/
theorem range_negHom (Q : Quantifier α) :
    Set.range (negHom · Q) = {Q, Q.innerNeg, Q.dual, Qᶜ} := by
  ext Q'
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨_ | _, _ | _⟩, rfl⟩ <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨(.positive, .positive), rfl⟩, ⟨(.positive, .negative), rfl⟩,
      ⟨(.negative, .negative), rfl⟩, ⟨(.negative, .positive), rfl⟩]

/-- Each image of `Q` under `negHom` has the same images as `Q`. -/
theorem range_negHom_negHom (p : Polarity × Polarity) (Q : Quantifier α) :
    Set.range (negHom · (negHom p Q)) = Set.range (negHom · Q) :=
  Set.ext fun _ ↦
    ⟨fun ⟨q, h⟩ ↦ ⟨q * p, (negHom_mul_apply q p Q).trans h⟩,
      fun ⟨q, h⟩ ↦ ⟨q * p⁻¹, (negHom_mul_apply _ p Q).symm.trans <|
        (congrArg (negHom · Q) (inv_mul_cancel_right q p)).trans h⟩⟩

end Quantifier

namespace Polarity.MonoBy

open Quantifier

variable {α : Type*} {Q : Quantifier α} {s : Polarity}

/-- If `Q` is directed by `s`, then `Polarity.complHom o Q` is directed by `o * s`. -/
protected theorem complHom (h : s.MonoBy Q) (o : Polarity) :
    (o * s).MonoBy (Polarity.complHom o Q) := by
  cases o
  · exact h
  · cases s
    exacts [fun _ _ hB hn hq ↦ hn (h hB hq), fun _ _ hB hn hq ↦ hn (h hB hq)]

/-- If `Q` is directed by `s`, then `innerNegHom i Q` is directed by `i * s`. -/
protected theorem innerNegHom (h : s.MonoBy Q) (i : Polarity) :
    (i * s).MonoBy (innerNegHom i Q) := by
  cases i
  · exact h
  · cases s
    exacts [fun _ _ hB ↦ h (Set.compl_subset_compl.2 hB),
      fun _ _ hB ↦ h (Set.compl_subset_compl.2 hB)]

/-- If `Q` is directed by `s`, then `negHom (o, i) Q` is directed by `o * i * s`. In particular
the dual of a monotone quantifier is monotone. -/
protected theorem negHom (h : s.MonoBy Q) (o i : Polarity) :
    (o * i * s).MonoBy (negHom (o, i) Q) := by
  rw [mul_assoc]
  exact (h.innerNegHom i).complHom o

end Polarity.MonoBy
