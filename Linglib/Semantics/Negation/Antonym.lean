module

public import Linglib.Logic.Aristotelian.Basic
public import Linglib.Semantics.Negation.Polarity
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype

/-!
# Negated antonyms

Sentential negation generates four forms from an antonym pair, *happy*, *not happy*, *unhappy* and
*not unhappy*: an `AntonymForm` is an adjective of either pole in a sentence of either polarity.
Its literal denotation is fixed by the extensions of the two poles, on which the polarity of the
sentence acts by complement. The extensions are contradictory, as those of *clean* and *dirty*
are, and each negated form [is synonymous with the simple form of the other
pole](##AntonymForm.denotation_smul_simple), or they are
[contrary](##AntonymForm.isContrary_iff_gap_nonempty), as those of *tall* and *short* are, and
[it adds the extension gap](##AntonymForm.denotation_negative_sdiff), in which *neither tall nor
short* [is literally true](##AntonymForm.denotation_notPositive_inter_notNegative).

## References

* [horn-1989]
* [kennedy-2007]
* [krifka-2007b]
* [cruse-1986]
-/

@[expose] public section

/-- An antonym form is one of the four surface forms that sentential negation generates from an
antonym pair, *happy*, *not happy*, *unhappy* and *not unhappy*: an adjective of either pole in a
sentence of either polarity. The type carries no semantics; `AntonymForm.denotation` reads a form
on the extensions of the two poles. -/
structure AntonymForm where
  /-- The pole of the adjective, positive for *happy* and negative for *unhappy*. -/
  pole : Polarity
  /-- The polarity of the sentence, negative under *not*. -/
  polarity : Polarity
  deriving Repr, DecidableEq, Fintype

namespace AntonymForm

/-- *happy* -/
@[match_pattern] abbrev positive : AntonymForm := ⟨.positive, .positive⟩

/-- *not happy* -/
@[match_pattern] abbrev notPositive : AntonymForm := ⟨.positive, .negative⟩

/-- *unhappy* -/
@[match_pattern] abbrev negative : AntonymForm := ⟨.negative, .positive⟩

/-- *not unhappy* -/
@[match_pattern] abbrev notNegative : AntonymForm := ⟨.negative, .negative⟩

/-- Case analysis on the four named forms. -/
@[elab_as_elim, cases_eliminator]
protected def cases {motive : AntonymForm → Sort*} (positive : motive .positive)
    (notPositive : motive .notPositive) (negative : motive .negative)
    (notNegative : motive .notNegative) : ∀ f, motive f
  | ⟨.positive, .positive⟩ => positive
  | ⟨.positive, .negative⟩ => notPositive
  | ⟨.negative, .positive⟩ => negative
  | ⟨.negative, .negative⟩ => notNegative

/-- The polarity of an antonym acts on the quadruplet through the pole, exchanging *happy* with
*unhappy* and *not happy* with *not unhappy*. -/
instance : MulAction Polarity AntonymForm where
  smul p f := ⟨p * f.pole, f.polarity⟩
  one_smul f := congrArg (AntonymForm.mk · f.polarity) (one_mul f.pole)
  mul_smul p q f := congrArg (AntonymForm.mk · f.polarity) (mul_assoc p q f.pole)

@[simp] theorem pole_smul (p : Polarity) (f : AntonymForm) : (p • f).pole = p * f.pole := rfl

@[simp] theorem polarity_smul (p : Polarity) (f : AntonymForm) : (p • f).polarity = f.polarity :=
  rfl

/-- `flip` exchanges the two poles of the quadruplet. -/
def flip (f : AntonymForm) : AntonymForm := Polarity.negative • f

@[simp] theorem negative_smul (f : AntonymForm) : Polarity.negative • f = f.flip := rfl

theorem flip_involutive : Function.Involutive flip := fun f ↦ by cases f <;> rfl

@[simp] theorem flip_flip (f : AntonymForm) : f.flip.flip = f := flip_involutive f

/-- The simple form that shares the literal meaning of a form when the poles are contradictory,
*happy* for *not unhappy* and *unhappy* for *not happy*: the two negations of a negated form
cancel into its pole (`denotation_smul_simple`). -/
def simple (f : AntonymForm) : AntonymForm := ⟨f.polarity * f.pole, .positive⟩

section Denotation
variable {D : Type*} {P N U : Set D}

/-- The literal denotation of a form, given the extension `ext p` of each pole: the polarity of
the sentence acts on the extension of the adjective's pole, sentential negation by complement.
What lies in neither extension is the extension gap. The poles are contradictory when their
extensions are complements, `ext p = p • U`, which [krifka-2007b] takes *happy* and *unhappy*
literally to be, and contrary when the extensions are disjoint with a gap, which the two standards
of a relative pair leave on [kennedy-2007]'s semantics and on [horn-1989]'s account of negated
antonyms. -/
def denotation (ext : Polarity → Set D) (f : AntonymForm) : Set D := f.polarity • ext f.pole

instance decidableMemDenotation (ext : Polarity → Set D) [∀ p, DecidablePred (· ∈ ext p)]
    (f : AntonymForm) : DecidablePred (· ∈ denotation ext f) :=
  Polarity.decidableMemSMul f.polarity (ext f.pole)

/-- On contradictory poles a form denotes by the product of its two polarities. -/
theorem denotation_smul (U : Set D) (f : AntonymForm) :
    denotation (· • U) f = (f.polarity * f.pole) • U :=
  (mul_smul ..).symm

/-- On contradictory poles each negated form is synonymous with the simple form of the other
pole, so double negation eliminates and *not unhappy* is *happy*. -/
@[simp] theorem denotation_smul_simple (U : Set D) (f : AntonymForm) :
    denotation (· • U) f.simple = denotation (· • U) f := by
  rw [denotation_smul, denotation_smul]
  exact congrArg (· • U) (one_mul _)

/-- *Neither happy nor unhappy* literally denotes the extension gap. -/
theorem denotation_notPositive_inter_notNegative (ext : Polarity → Set D) :
    denotation ext .notPositive ∩ denotation ext .notNegative =
      (ext .positive ∪ ext .negative)ᶜ :=
  (Set.compl_union ..).symm

/-- What a negated form adds to the extension of the other pole is the extension gap. -/
theorem denotation_negative_sdiff (ext : Polarity → Set D) (p : Polarity) :
    denotation ext ⟨p, .negative⟩ \ ext (.negative * p) = (ext .positive ∪ ext .negative)ᶜ := by
  cases p
  · show (ext .positive)ᶜ \ ext .negative = _
    rw [Set.compl_union, Set.sdiff_eq]
  · show (ext .negative)ᶜ \ ext .positive = _
    rw [Set.compl_union, Set.sdiff_eq, Set.inter_comm]

open Aristotelian in
/-- Disjoint extensions are contrary exactly when they leave a gap. -/
theorem isContrary_iff_gap_nonempty (hPN : Disjoint P N) :
    IsContrary P N ↔ (P ∪ N)ᶜ.Nonempty := by
  rw [IsContrary, and_iff_right hPN, codisjoint_iff]
  exact Set.nonempty_compl.symm

end Denotation

end AntonymForm
