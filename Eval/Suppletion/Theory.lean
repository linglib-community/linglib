module

public import Linglib.Morphology.Exponence.Containment.Contiguity
public import Linglib.Morphology.Paradigm.Contiguity

/-!
# Theories of root suppletion

Three theories say which root patterns a three-cell containment hierarchy can show, whether its
cells are the grades of an adjective or the cases or numbers of a pronoun (`Theory.Generates`).
Elsewhere insertion over the hierarchy generates the contiguous patterns, Bobaljik's containment
with an antihomophonous and grounded vocabulary generates AAA, ABB and ABC
(`groundedGenerable_iff`), and a theory of the cells as independent generates every pattern. A
theory fits a pattern under a parse, which gives the cell whose structure each cell's word
realizes, when a pattern it generates, read through the parse, classes the cells as the pattern
does (`Theory.Fits`).

## TODO

The domain locality of Smith, Moskal, Xu, Kang and Bobaljik (`SmithMoskalEtAl2019.DomainLocal`)
is not registered. Its no-AAB plateau over degree is proved for terminal vocabularies, while an
ABC triple needs a portmanteau, so its predictions over degree wait on the paper's treatment of
portmanteaus.

## References

* [bobaljik-2012]
* [smith-moskal-xu-kang-bobaljik-2019]
-/

@[expose] public section

namespace Eval.Suppletion

open Morphology Morphology.Exponence Morphology.Containment

/-- Three theories of the root patterns of a three-cell hierarchy. -/
inductive Theory
  /-- Elsewhere insertion over the containment hierarchy, from terminal antihomophonous rules. -/
  | elsewhere
  /-- Bobaljik's containment, with an antihomophonous and grounded vocabulary. -/
  | grounded
  /-- The cells as independent, without containment. -/
  | free
  deriving DecidableEq, Repr

/-- A theory generates a root pattern on the three cells of a hierarchy, for degree the three
synthetic grades. -/
def Theory.Generates : Theory → Paradigm 3 ℕ → Prop
  | .elsewhere, p => ElsewhereGenerable p
  | .grounded, p => GroundedGenerable p
  | .free, _ => True

instance : ∀ T : Theory, DecidablePred T.Generates
  | .elsewhere => fun p ↦ decidable_of_iff _
      ((isContiguous_fin_three_iff p).symm.trans (isContiguous_iff_generable p))
  | .grounded => fun p ↦ decidable_of_iff ((p 0 = p 2 → p 0 = p 1) ∧ ¬ (p 0 = p 1 ∧ p 1 ≠ p 2))
      (by rw [Theory.Generates, groundedGenerable_iff, isContiguous_fin_three_iff])
  | .free => fun _ ↦ isTrue trivial

/-- The theories that rest on containment, under which Merger reaches the comparative before the
superlative. -/
def Theory.Containment : Theory → Prop
  | .elsewhere | .grounded => True
  | .free => False

instance : DecidablePred Theory.Containment
  | .elsewhere | .grounded => isTrue trivial
  | .free => isFalse id

/-- The five root patterns over three cells, one of each class. -/
def shapes : List (Paradigm 3 ℕ) := [Paradigm.aaa, Paradigm.abb, Paradigm.abc, Paradigm.aba,
  Paradigm.aab]

/-- A theory fits a root pattern under a parse `e`, giving the grade whose structure the root's
word realizes in each cell, when a pattern it generates, read through `e`, classes the grades as
the root pattern does. -/
def Theory.Fits (T : Theory) (e : Fin 3 → Fin 3) (p : Paradigm 3 ℕ) : Prop :=
  ∃ q ∈ shapes, T.Generates q ∧ Setoid.ker (q ∘ e) = Setoid.ker p

instance (T : Theory) (e : Fin 3 → Fin 3) (p : Paradigm 3 ℕ) : Decidable (T.Fits e p) :=
  decidable_of_iff (∃ q ∈ shapes, T.Generates q ∧ (q (e 0) = q (e 1) ↔ p 0 = p 1) ∧
      (q (e 1) = q (e 2) ↔ p 1 = p 2) ∧ (q (e 0) = q (e 2) ↔ p 0 = p 2)) <| by
    simp only [Theory.Fits, ker_eq_ker_iff_fin_three, Function.comp_apply]

end Eval.Suppletion
