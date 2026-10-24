/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Character
public import Linglib.Semantics.Reference.Nominal
public import Linglib.Semantics.Reference.Iota

/-!
# Donnellan (1966): Reference and Definite Descriptions

Donnellan distinguishes two uses of a definite description. Used attributively, *the φ* denotes
at each world whoever uniquely satisfies φ there, the Russellian iota taken pointwise
(`attributive`, `attributive_eq_some_iff`), and as a nominal denotation its only presupposition
is that the iota is defined (`attributiveNominal`, `attributiveNominal_resolve_eq_one_iff`). Used
referentially, it denotes the individual the speaker has in mind whatever the world: the
constant character (`Character.const`), whose content is rigid.
The two uses come apart in Donnellan's scene of the man with the martini: when the intended
referent fails the description at a world where someone else uniquely satisfies it, the
attributive use denotes that other individual and the referential use the intended one
(`attributive_ne_const_of_misfit`).

## Implementation notes

Whether the referential use is semantic or pragmatic, the dispute with Kripke, is not decided
here: the file gives Donnellan's truth conditions for each use.

## References

* [donnellan-1966]
* [kripke-1977]
* [russell-1905]
-/

@[expose] public section

namespace Donnellan1966

open Kaplan

variable {W E : Type*} {φ : E → W → Prop} {w : W} {e intended : E}

/-- The attributive use, which picks out at each world the unique satisfier of the description
there. -/
noncomputable def attributive (φ : E → W → Prop) : W → Option E := fun w ↦ iota (φ · w)

theorem attributive_eq_some_iff : attributive φ w = some e ↔ φ e w ∧ ∀ x, φ x w → x = e :=
  iota_eq_some_iff _

/-- The attributive use as a nominal denotation, whose selector is the pointwise iota and which
presupposes nothing beyond the iota's definedness. -/
noncomputable def attributiveNominal (φ : E → W → Prop) : Nominal Unit W E :=
  .ofReferent (attributive φ)

theorem attributiveNominal_resolve_eq_one_iff (ψ : E → W → Prop) (h : attributive φ w = some e) :
    (attributiveNominal φ).resolve ψ () w = 1 ↔ ψ e w := by
  simp [attributiveNominal, Nominal.ofReferent_resolve, Presupposition.presupOfReferent_of_some h]

theorem attributive_ne_const_of_misfit (h : attributive φ w = some e) (hne : e ≠ intended) :
    attributive φ w ≠ some (Character.const intended () w) := by
  simpa [h] using hne

end Donnellan1966
