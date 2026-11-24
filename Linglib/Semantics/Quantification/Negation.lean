module

public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Negation.Polarity
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The negations of a quantifier as an action of the polarities

A quantifier has two polarities, one for its value and one for its scope. Reversing the first is
outer negation, the complement `Qᶜ`; reversing the second is inner negation, `Q.innerNeg`, which
complements the scope; reversing both is the dual. The two commute, so a pair of polarities acts
on the quantifiers on a universe, and the square of opposition that a quantifier spans is its
orbit: each of its members spans the same square. A pair of polarities changes the direction of a
monotone or antitone quantifier by the product of the two.

## Main definitions

* `Quantifier.innerNegHom`: the polarities acting on quantifiers through the scope.
* `Quantifier.negHom`: the pairs of an outer and an inner polarity acting on quantifiers.

## Main results

* `Quantifier.range_negHom`: the orbit of a quantifier is its inner negation, its dual, its
  complement and itself, the corners of `Quantifier.square`.
* `Quantifier.range_negHom_negHom`: each member of a square spans the same square.
* `Polarity.MonoBy.negHom`: a quantifier directed by `s` is, after the outer polarity `o` and the
  inner polarity `i`, directed by `o * i * s`.

## Implementation notes

The action is stated as a homomorphism into `Function.End (Quantifier α)` and not as a `MulAction`
instance: `Quantifier α` unfolds to the function type `Set α → Prop`, on which an instance would
apply to every function from sets to propositions.

## References

* [peters-westerstahl-2006]
-/

@[expose] public section

namespace Quantifier

variable {α : Type*} {Q : Quantifier α}

/-- The polarities act on quantifiers through the scope: the negative polarity is inner
negation. -/
def innerNegHom : Polarity →* Function.End (Quantifier α) :=
  Polarity.lift ⟨innerNeg, (show Function.Involutive innerNeg from innerNeg_innerNeg).comp_self⟩

@[simp] theorem innerNegHom_positive (Q : Quantifier α) : innerNegHom .positive Q = Q := rfl

@[simp] theorem innerNegHom_negative (Q : Quantifier α) : innerNegHom .negative Q = Q.innerNeg :=
  rfl

/-- A pair of an outer and an inner polarity acts on quantifiers: the outer one through the value,
by complement, and the inner one through the scope. -/
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

/-- The orbit of a quantifier under the polarities is the square it spans. -/
theorem range_negHom (Q : Quantifier α) :
    Set.range (negHom · Q) = {Q, Q.innerNeg, Q.dual, Qᶜ} := by
  ext Q'
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨_ | _, _ | _⟩, rfl⟩ <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨(.positive, .positive), rfl⟩, ⟨(.positive, .negative), rfl⟩,
      ⟨(.negative, .negative), rfl⟩, ⟨(.negative, .positive), rfl⟩]

/-- Each quantifier in the square of `Q` spans the same square. -/
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

/-- The outer polarity `o` takes a quantifier directed by `s` to one directed by `o * s`. -/
protected theorem complHom (h : s.MonoBy Q) (o : Polarity) :
    (o * s).MonoBy (Polarity.complHom o Q) := by
  cases o
  · exact h
  · cases s
    exacts [fun _ _ hB hn hq ↦ hn (h hB hq), fun _ _ hB hn hq ↦ hn (h hB hq)]

/-- The inner polarity `i` takes a quantifier directed by `s` to one directed by `i * s`. -/
protected theorem innerNegHom (h : s.MonoBy Q) (i : Polarity) :
    (i * s).MonoBy (innerNegHom i Q) := by
  cases i
  · exact h
  · cases s
    exacts [fun _ _ hB ↦ h (Set.compl_subset_compl.2 hB),
      fun _ _ hB ↦ h (Set.compl_subset_compl.2 hB)]

/-- The outer polarity `o` and the inner polarity `i` take a quantifier directed by `s` to one
directed by `o * i * s`, so that the dual of a monotone quantifier is monotone. -/
protected theorem negHom (h : s.MonoBy Q) (o i : Polarity) :
    (o * i * s).MonoBy (negHom (o, i) Q) := by
  rw [mul_assoc]
  exact (h.innerNegHom i).complHom o

end Polarity.MonoBy
