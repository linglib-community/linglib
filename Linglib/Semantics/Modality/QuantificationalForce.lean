module

public import Linglib.Semantics.Modality.Basic
public import Mathlib.Order.Filter.Basic

/-!
# Claims of a quantificational force

A modal of universal force claims that its prejacent is a necessity, and one of existential force
that the negation of its prejacent is not. In this file we define

* `QuantificationalForce.claim N p q`: the set of worlds `w` at which a modal of force `q` holds
  of the proposition `p`, where `N w` is the filter of necessities at `w`.

## Main statements

* `QuantificationalForce.antitone_claim`: over consistent necessities, the universal
  claim entails the existential one.
* `QuantificationalForce.compl_claim`: the negation of a claim is the dual claim about
  the negated prejacent.
-/

@[expose] public section

namespace Modality

open Filter

variable {W : Type*} {w : W}

namespace QuantificationalForce

variable (N : W → Filter W) (p : Set W)

/-- The claim a modal of quantificational force `q` makes about `p` over the necessities `N`: that
`p` is a necessity, or that its negation is not. -/
def claim : QuantificationalForce → Set W
  | .universal => {w | p ∈ N w}
  | .existential => {w | ∃ᶠ v in N w, v ∈ p}

variable {N p}

@[simp] theorem mem_claim_universal : w ∈ claim N p .universal ↔ p ∈ N w := .rfl

@[simp] theorem mem_claim_existential : w ∈ claim N p .existential ↔ ∃ᶠ v in N w, v ∈ p := .rfl

/-- Over consistent necessities the universal claim entails the existential one. -/
theorem antitone_claim (hN : ∀ w, (N w).NeBot) : Antitone (claim N p) := by
  intro q r hqr w hw
  have := hN w
  cases q <;> cases r
  exacts [hw, Eventually.frequently hw, absurd hqr (by decide), hw]

variable (N p)

/-- The negation of a claim is the dual claim about the negated prejacent. -/
theorem compl_claim (q : QuantificationalForce) : (claim N p q)ᶜ = claim N pᶜ q.dual := by
  ext w
  cases q
  exacts [not_frequently, not_eventually]

end QuantificationalForce

end Modality
