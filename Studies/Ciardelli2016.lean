/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Concept

/-!
# Ciardelli (2016): Lifting Conditionals to Inquisitive Semantics

An account of conditionals that assigns them propositions is an operation `imp` sending two
propositions `a` and `b` to the conditional proposition `imp a b`. In inquisitive semantics a
sentence has a set of alternatives, and the lifted conditional with antecedent alternatives `A`
and consequent alternatives `B` is supported by an information state `s` when for every
`a ∈ A` there is a `b ∈ B` with `s ⊆ imp a b`. The supporting states are `support imp A B`.

Where antecedent and consequent each have one alternative the lifted account is the account it
lifts (`support_singleton`). A disjunctive antecedent with two alternatives is supported exactly
where the conditionals from both are (`support_pair_left`), and a polar question in the
consequent where one of the two conditionals is (`support_pair_right`). With one consequent
alternative, the supporting states are the subsets of the upper polar of the antecedent
alternatives along `fun a w ↦ w ∈ imp a r` (`support_singleton_right`).

## Implementation notes

The alternatives of antecedent and consequent are given as sets of propositions and are not
computed from sentences, so the projection operators and the presuppositions of unconditionals
are not represented.

## References

* [ciardelli-2016]
* [alonso-ovalle-2009]
-/

@[expose] public section

namespace Ciardelli2016

variable {W : Type*} (imp : Set W → Set W → Set W)

/-- The states supporting the conditional with antecedent alternatives `A` and consequent
alternatives `B`. -/
def support (A B : Set (Set W)) : Set (Set W) := {s | ∀ a ∈ A, ∃ b ∈ B, s ⊆ imp a b}

variable {imp} {A B : Set (Set W)} {p q r s t : Set W}

-- persistence
theorem support_anti (h : t ⊆ s) (hs : s ∈ support imp A B) : t ∈ support imp A B :=
  fun a ha ↦ let ⟨b, hb, hsb⟩ := hs a ha; ⟨b, hb, h.trans hsb⟩

-- (5a)
theorem support_singleton : s ∈ support imp {p} {r} ↔ s ⊆ imp p r := by
  simp [support]

/-- (5b), *if they play Bach or Handel, Alice will go*, the two disjuncts being independent and
so both alternatives: the state supports the conditional from each. -/
theorem support_pair_left : s ∈ support imp {p, q} {r} ↔ s ⊆ imp p r ∩ imp q r := by
  simp [support, Set.subset_inter_iff]

/-- (5e), *if they play Bach, will Alice go?*: the state settles the conditional one way or the
other, so the alternatives of the question are the two conditionals. -/
theorem support_pair_right : s ∈ support imp {p} {r, rᶜ} ↔ s ⊆ imp p r ∨ s ⊆ imp p rᶜ := by
  simp [support]

/-- With one consequent alternative the supporting states are those included in the upper polar
of the alternatives of the antecedent. -/
theorem support_singleton_right :
    s ∈ support imp A {r} ↔ s ⊆ upperPolar (fun a w ↦ w ∈ imp a r) A := by
  simp only [support, Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left]
  exact ⟨fun h w hw a ha ↦ h a ha hw, fun h a ha w hw ↦ h hw ha⟩

end Ciardelli2016
