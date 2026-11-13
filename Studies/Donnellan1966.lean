/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Character
public import Linglib.Semantics.Reference.Definite
public import Linglib.Semantics.Reference.Iota

/-!
# Donnellan (1966): Reference and Definite Descriptions

Donnellan distinguishes two uses of a definite description. Used attributively, *the φ* denotes
at each world whoever uniquely satisfies φ there, the Russellian iota taken pointwise
(`attributive`, `mem_attributive`), and as a definite denotation it denotes where the
iota is defined (`attributiveDefinite`, `attributiveDefinite_toTrivalent_eq_true_iff`). Used
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


variable {W E : Type*} {φ : E → W → Prop} {w : W} {e intended : E}

/-- The attributive use, which picks out at each world the unique satisfier of the description
there. -/
noncomputable def attributive (φ : E → W → Prop) : W → Part E := fun w ↦ iota {x | φ x w}

theorem mem_attributive : e ∈ attributive φ w ↔ φ e w ∧ ∀ x, φ x w → x = e :=
  mem_iota

/-- The attributive use as a definite denotation, the pointwise iota where it is defined. -/
noncomputable def attributiveDefinite (φ : E → W → Prop) : Definite Unit W E :=
  fun _ ↦ attributive φ

theorem attributiveDefinite_toTrivalent_eq_true_iff (ψ : E → W → Prop)
    (h : e ∈ attributive φ w) :
    (attributiveDefinite φ).toTrivalent ψ () w = .true ↔ ψ e w :=
  Definite.toTrivalent_eq_true_iff.trans
    ⟨fun ⟨_, he', h'⟩ ↦ Part.mem_unique he' h ▸ h', fun h' ↦ ⟨e, h, h'⟩⟩

theorem attributive_ne_const_of_misfit (h : e ∈ attributive φ w) (hne : e ≠ intended) :
    attributive φ w ≠ Part.some (Character.const intended () w) :=
  fun heq ↦ hne (Part.mem_some_iff.1 (heq ▸ h))

end Donnellan1966
