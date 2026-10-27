/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Exhaustification.Finite

/-!
# Pre-exhaustified alternatives

The grammatical theory of implicature negates *pre-exhaustified* subdomain alternatives, each
alternative exhaustified against the alternative set before it is negated. `preExhaustify O C`
collects the alternatives of `C`, each exhaustified by the operator `O` against `C`. Chierchia
uses innocent exclusion, which `Excluder.preExhaustify` computes over finite worlds
(`asSetOfSets_preExhaustify_innocent`). Over an irredundant family a pre-exhaustified alternative
holds just where its own member holds and no other does (`Irredundant.mem_exh_range_iff`), the form
`exhAgainst (· ≠ ·)` in which papers negate them under a modal.

## Main definitions

* `Exhaustification.preExhaustify`: each alternative exhaustified against the set.
* `Exhaustification.Excluder.preExhaustify`: the same over finite worlds.

## References

* [chierchia-2013]
* [fox-2007]
-/

@[expose] public section

namespace Exhaustification

variable {W : Type*}

/-- The alternatives of `C`, each exhaustified by `O` against `C`. -/
def preExhaustify (O : Set (Set W) → Set W → Set W) (C : Set (Set W)) : Set (Set W) :=
  O C '' C

variable [Fintype W] [DecidableEq W]

/-- The alternatives of `ALT`, each exhaustified by the excluder `E` against `ALT`. -/
def Excluder.preExhaustify (E : Excluder W) (ALT : Finset (Finset W)) : Finset (Finset W) :=
  ALT.image (E.exh ALT)

theorem asSetOfSets_preExhaustify_innocent (ALT : Finset (Finset W)) :
    (innocent.preExhaustify ALT).toSetFamily = preExhaustify exhIE ALT.toSetFamily := by
  ext s
  simp only [Finset.mem_toSetFamily, Excluder.preExhaustify, Finset.mem_image, preExhaustify,
    Set.mem_image]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ⟨a, ha, rfl⟩, (coe_innocent_exh ALT a).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, coe_innocent_exh ALT a⟩

end Exhaustification
