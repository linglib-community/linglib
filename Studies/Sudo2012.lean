module

public import Linglib.Core.Control.Monad.Writer
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.Nontrivial.Defs

/-!
# Sudo (2012): On the semantics of phi features on pronouns

The gender of a pronoun is presupposed, and for a predicate such as *criticized herself* what
is presupposed, that the subject is female, is independent of what is asserted, that the subject
criticized herself. Sudo argues that theories on which a presupposition makes a predicate
partial or three-valued cannot express the meaning of *Exactly one student criticized herself*,
which counts the students who criticized themselves whatever their gender: on those theories the
predicate [is the same](##Sudo2012.toPart_criticizedHerself) as *is female and criticized
herself*, and [no quantifier](##Sudo2012.not_existsUnique_factors_toPart) recovers the count
from it. The presupposition has to be a second dimension of meaning, as in Karttunen and Peters.

## Implementation notes

A two-dimensional truth value is a computation of the writer monad over truth values, its log
the presupposition, and the theories are compared along `Writer.toPart`. A partial truth value
stands in for a three-valued one, the two being equivalent.

## TODO

* The thesis answers the binding problem that a two-dimensional theory faces in quantified
  sentences with cross-sentential anaphora; that proposal is not formalized.

## References

* [Y. Sudo, *On the semantics of phi features on pronouns* (2012)][sudo-2012]
* [L. Karttunen and S. Peters, *Conventional implicature* (1979)][karttunen-peters-1979]
-/

@[expose] public section

namespace Sudo2012

variable {E : Type}

/-- *Criticized herself* in two dimensions asserts that `x` criticized `x` and presupposes that
`x` is female. -/
def criticizedHerself (criticized : E → E → Prop) (female : Set E) (x : E) : Writer Prop Prop :=
  Writer.mk (criticized x x) (x ∈ female)

-- (186), (187)
/-- As a partial predicate, *criticized herself* is *is female and criticized herself*. -/
theorem toPart_criticizedHerself (criticized : E → E → Prop) (female : Set E) (x : E) :
    (criticizedHerself criticized female x).toPart =
      (Writer.mk (x ∈ female ∧ criticized x x) (x ∈ female)).toPart :=
  Writer.toPart_eq_iff.2 ⟨Iff.rfl, fun hx ↦ propext ⟨fun h ↦ ⟨hx, h⟩, fun h ↦ h.2⟩⟩

-- (185)
/-- No quantifier over partial predicates computes, from the partial predicate of a
two-dimensional one, whether exactly one individual satisfies its assertion. -/
theorem not_existsUnique_factors_toPart [Nontrivial E] :
    ¬ ∃ Q : (E → Part Prop) → Prop, ∀ P : E → Writer Prop Prop,
      Q (fun x ↦ (P x).toPart) ↔ ∃! x, (P x).val := by
  rintro ⟨Q, hQ⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  have h₁ := hQ (criticizedHerself (fun _ _ ↦ True) {a})
  have h₂ := hQ fun x ↦ Writer.mk (x ∈ ({a} : Set E) ∧ True) (x ∈ ({a} : Set E))
  rw [funext (toPart_criticizedHerself (fun _ _ ↦ True) {a}), h₂] at h₁
  exact hab ((h₁.1 ⟨a, ⟨rfl, trivial⟩, fun _ h ↦ h.1⟩).unique trivial trivial)

end Sudo2012
