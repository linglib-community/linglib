module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Finset.Basic

/-!
# Belief and complement worlds

The world space of the *know*/*think* projection experiments: a world records whether the
attitude holder believes the complement and whether the complement is true. *Know* holds at a
world when both do and *think* when the first does, so *know* entails the complement and
entails *think*, the factive against non-factive contrast of [kiparsky-kiparsky-1970]. The two
questions of the experiments ask for the two coordinates, and a speaker assumes the complement
when it is true throughout an information state.

## References

* [kiparsky-kiparsky-1970]
* [scontras-tonhauser-2025]
* [grove-white-2025]
-/

@[expose] public section

namespace Factivity

/-- A world of the projection experiments records whether the attitude holder believes the
complement and whether it is true, as the pair of the two truth values, so that a prior over
worlds can be a product measure. -/
abbrev World := Bool × Bool

/-- The attitude holder believes the complement. -/
abbrev World.believes (w : World) : Bool := w.1

/-- The complement is true. -/
abbrev World.complement (w : World) : Bool := w.2

variable {w : World}

/-- *X knows C* holds when *X* believes the complement and it is true. -/
def World.Knows (w : World) : Prop := w.believes ∧ w.complement

instance : DecidablePred World.Knows := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- *X thinks C* holds when *X* believes the complement. -/
def World.Thinks (w : World) : Prop := w.believes

instance : DecidablePred World.Thinks := fun _ ↦ inferInstanceAs (Decidable (_ = true))

theorem World.Knows.complement (h : w.Knows) : w.complement = true := h.2

theorem World.Knows.thinks (h : w.Knows) : w.Thinks := h.1

/-- The two questions of the experiments, whether *X* believes the complement and whether it is
true. -/
inductive Question where
  | belief
  | complement
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The answer a world gives to a question. -/
def Question.answer : Question → World → Bool
  | .belief, w => w.believes
  | .complement, w => w.complement

/-- The speaker assumes the complement when it is true throughout the information state. -/
def AssumesComplement (S : Finset World) : Prop := ∀ w ∈ S, w.complement = true

instance : DecidablePred AssumesComplement := fun _ ↦ inferInstanceAs (Decidable (∀ w ∈ _, _))

end Factivity
