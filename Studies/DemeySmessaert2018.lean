module

public import Linglib.Core.Order.BooleanSubalgebra
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod

/-!
# Demey and Smessaert 2018

Demey and Smessaert compute the bitstring semantics of a finite fragment from the partition the
fragment induces, without first computing its Boolean closure. In their Example 2 the fragment
`{p ∧ q, ¬p ∨ ¬q, p ∨ q, ¬p ∧ ¬q}` of classical propositional logic has sixteen conjunctions of
literals, of which three are consistent, so its closure has `2 ^ 3` elements. Their partition
is `Finpartition.minterms` and their bitstring semantics `BooleanSubalgebra.toSetOfMinterms`.

## Implementation notes

A proposition over `p` and `q` is the finset of valuations making it true, a valuation being the
pair of truth values of `p` and `q`.

## References

* [demey-smessaert-2018]
-/

@[expose] public section

namespace DemeySmessaert2018

open Finset

/-- The proposition `p` holds at the valuations that make `p` true. -/
def p : Finset (Bool × Bool) := univ.filter (·.1)

/-- The proposition `q` holds at the valuations that make `q` true. -/
def q : Finset (Bool × Bool) := univ.filter (·.2)

/-- The fragment of Example 2 is `{p ∧ q, ¬p ∨ ¬q, p ∨ q, ¬p ∧ ¬q}`. -/
def example2 : Fin 4 → Finset (Bool × Bool) := ![p ⊓ q, pᶜ ⊔ qᶜ, p ⊔ q, pᶜ ⊓ qᶜ]

/-- The fragment of Example 2 induces the three anchors `p ∧ q`, `(p ∨ q) ∧ (¬p ∨ ¬q)` and
`¬p ∧ ¬q`. -/
theorem parts_minterms_example2 :
    (Finpartition.minterms example2).parts = {p ⊓ q, (p ⊔ q) ⊓ (pᶜ ⊔ qᶜ), pᶜ ⊓ qᶜ} := by
  decide

-- Theorem 1: the closure of Example 2 has eight elements.
example : Nat.card (BooleanSubalgebra.closure (Set.range example2)) = 8 := by
  rw [BooleanSubalgebra.card_closure, parts_minterms_example2]
  decide

end DemeySmessaert2018
