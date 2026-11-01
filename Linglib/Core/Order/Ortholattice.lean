/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.ModularLattice
public import Linglib.Core.Order.InvolutiveCompl

/-!
# Orthocomplemented and orthomodular lattices

This file defines orthocomplemented lattices, or ortholattices, and orthomodular lattices. An
*ortholattice* is a bounded lattice with an involutive, order-reversing complement `ᶜ` satisfying
non-contradiction, `a ⊓ aᶜ = ⊥`, and so, by De Morgan, excluded middle, `a ⊔ aᶜ = ⊤`.

Heyting algebras and ortholattices weaken Boolean algebras in opposite directions. A Heyting
algebra keeps distributivity and the pseudocomplement law `a ⊓ b = ⊥ → b ≤ aᶜ` but gives up the
involution; an ortholattice keeps the involution and the complement laws but gives up
distributivity. They meet in the Boolean algebras, since [an ortholattice is distributive exactly
when its orthocomplement is a pseudocomplement](##inf_sup_le_iff_le_compl_of_disjoint).

An ortholattice is *orthomodular* when `a ≤ b` implies `b = a ⊔ (aᶜ ⊓ b)`. Every modular
ortholattice, and so every Boolean algebra, is orthomodular. The motivating example is the lattice
of closed subspaces of a Hilbert space, Birkhoff and von Neumann's propositions of quantum
mechanics. The regular propositions of Holliday and Mandelkern's epistemic compatibility frames
form an ortholattice that is not orthomodular.

## Main definitions

* `IsOrtholattice α`: the Prop mixin over `[Lattice α] [BoundedOrder α] [InvolutiveCompl α]`
  (the involutive antitone `ᶜ` of `Core/Order/InvolutiveCompl.lean`) adding
  non-contradiction.
* `IsOrthomodularLattice α`: an ortholattice satisfying the orthomodular law.

## Main results

* `IsOrtholattice.inf_sup_le_iff_le_compl_of_disjoint`: an ortholattice is distributive exactly
  when its orthocomplement is a pseudocomplement.
* `IsModularLattice.toIsOrthomodularLattice`: a modular ortholattice is orthomodular.

## TODO

Upstream candidate for `Mathlib/Order/Ortholattice.lean`. The mathlib instance is the lattice of
closed subspaces of a Hilbert space, in `Mathlib/Analysis/InnerProductSpace/Projection/`:
`ClosedSubmodule.orthogonal` is an `InvolutiveCompl` by `ClosedSubmodule.orthogonal_orthogonal_eq`
and `ClosedSubmodule.orthogonal_le`, non-contradiction is `ClosedSubmodule.inf_orthogonal_eq_bot`,
and orthomodularity is `Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection`.

## References

* [birkhoff-von-neumann-1936]
* [holliday-mandelkern-2024]
-/

@[expose] public section

variable {α : Type*}

/-- An **ortholattice** is a bounded lattice whose involutive complement satisfies
non-contradiction, `a ⊓ aᶜ ≤ ⊥` ([holliday-mandelkern-2024] Definition 3.3). It is the sibling of
mathlib's `ComplementedLattice` with the complement chosen by `ᶜ`. Excluded middle follows by De
Morgan, `IsOrtholattice.top_le_sup_compl`. -/
class IsOrtholattice (α : Type*) [Lattice α] [BoundedOrder α] [InvolutiveCompl α] : Prop where
  /-- Every element is disjoint from its complement, `a ⊓ aᶜ ≤ ⊥`. -/
  protected inf_compl_le_bot (a : α) : a ⊓ aᶜ ≤ ⊥

namespace IsOrtholattice

/- The involutive-antitone consequences (De Morgan, injectivity, `le_compl_comm`, ...) are
inherited from the shared base: use the `InvolutiveCompl.*` names. -/

variable [Lattice α] [BoundedOrder α] [InvolutiveCompl α] [IsOrtholattice α] {a b : α}

@[simp]
protected theorem inf_compl_eq_bot (a : α) : a ⊓ aᶜ = ⊥ :=
  le_bot_iff.1 (IsOrtholattice.inf_compl_le_bot a)

protected theorem top_le_sup_compl (a : α) : ⊤ ≤ a ⊔ aᶜ := by
  rw [← InvolutiveCompl.compl_le_compl_iff_le, InvolutiveCompl.compl_sup,
    InvolutiveCompl.compl_compl, InvolutiveCompl.compl_top, inf_comm]
  exact IsOrtholattice.inf_compl_le_bot a

@[simp]
protected theorem sup_compl_eq_top (a : α) : a ⊔ aᶜ = ⊤ :=
  top_le_iff.1 (IsOrtholattice.top_le_sup_compl a)

protected theorem isCompl_compl (a : α) : IsCompl a aᶜ :=
  .of_eq (IsOrtholattice.inf_compl_eq_bot a) (IsOrtholattice.sup_compl_eq_top a)

protected theorem disjoint_compl_right (a : α) : Disjoint a aᶜ :=
  (IsOrtholattice.isCompl_compl a).disjoint

/-- Orthogonal elements are disjoint. The converse, the pseudocomplement law,
[characterizes distributivity](##inf_sup_le_iff_le_compl_of_disjoint). -/
protected theorem disjoint_of_le_compl (h : a ≤ bᶜ) : Disjoint a b :=
  (IsOrtholattice.disjoint_compl_right b).symm.mono_left h

/-- An ortholattice is distributive exactly when its orthocomplement is a pseudocomplement,
`a ⊓ b = ⊥ → b ≤ aᶜ` ([holliday-mandelkern-2024] Proposition 3.7). -/
theorem inf_sup_le_iff_le_compl_of_disjoint :
    (∀ a b c : α, a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c) ↔ ∀ a b : α, Disjoint a b → b ≤ aᶜ := by
  refine ⟨fun h a b hab ↦ ?_, fun h a b c ↦ ?_⟩
  · calc b = b ⊓ (a ⊔ aᶜ) := by rw [IsOrtholattice.sup_compl_eq_top, inf_top_eq]
      _ ≤ b ⊓ a ⊔ b ⊓ aᶜ := h b a aᶜ
      _ ≤ aᶜ := sup_le ((disjoint_iff_inf_le.1 hab.symm).trans bot_le) inf_le_right
  suffices ∀ d, a ⊓ b ≤ d → a ⊓ c ≤ d → a ⊓ (b ⊔ c) ≤ d from this _ le_sup_left le_sup_right
  intro d hb hc
  have key (e : α) (he : a ⊓ e ≤ d) : a ⊓ dᶜ ≤ eᶜ := h e _ <| disjoint_iff_inf_le.2 <|
    (le_inf ((le_inf (inf_le_right.trans inf_le_left) inf_le_left).trans he)
      (inf_le_right.trans inf_le_right)).trans (IsOrtholattice.inf_compl_le_bot d)
  have hbc : a ⊓ dᶜ ≤ (b ⊔ c)ᶜ := by
    rw [InvolutiveCompl.compl_sup]
    exact le_inf (key b hb) (key c hc)
  simpa only [InvolutiveCompl.compl_compl] using h dᶜ _ <| disjoint_iff_inf_le.2 <|
    (le_inf (inf_le_right.trans inf_le_right)
      ((le_inf (inf_le_right.trans inf_le_left) inf_le_left).trans hbc)).trans
      (IsOrtholattice.inf_compl_le_bot _)

end IsOrtholattice

/-- Every ortholattice is complemented, with `ᶜ` as the chosen complement. -/
instance (priority := 100) IsOrtholattice.toComplementedLattice [Lattice α] [BoundedOrder α]
    [InvolutiveCompl α] [IsOrtholattice α] : ComplementedLattice α :=
  ⟨fun a ↦ ⟨aᶜ, IsOrtholattice.isCompl_compl a⟩⟩

/-- Every Boolean algebra is orthocomplemented. -/
instance (priority := 100) BooleanAlgebra.toIsOrtholattice [BooleanAlgebra α] : IsOrtholattice α :=
  ⟨BooleanAlgebra.inf_compl_le_bot⟩

/-! ### Orthomodular lattices -/

/-- An **orthomodular lattice** is an ortholattice in which `a ≤ b` implies
`b = a ⊔ (aᶜ ⊓ b)` ([holliday-mandelkern-2024] Definition 3.5). We only require `≤`, since the
other inequality holds in every lattice. -/
class IsOrthomodularLattice (α : Type*) [Lattice α] [BoundedOrder α] [InvolutiveCompl α] : Prop
    extends IsOrtholattice α where
  /-- If `a ≤ b`, then `b ≤ a ⊔ (aᶜ ⊓ b)`. -/
  protected le_sup_compl_inf_of_le {a b : α} : a ≤ b → b ≤ a ⊔ aᶜ ⊓ b

section IsOrthomodularLattice

variable [Lattice α] [BoundedOrder α] [InvolutiveCompl α]

/-- A modular ortholattice is orthomodular ([holliday-mandelkern-2024] footnote 4), and so,
through `DistribLattice`, is every Boolean algebra. -/
instance (priority := 100) IsModularLattice.toIsOrthomodularLattice [IsOrtholattice α]
    [IsModularLattice α] : IsOrthomodularLattice α where
  le_sup_compl_inf_of_le {a _} h := by
    simpa only [IsOrtholattice.sup_compl_eq_top, top_inf_eq] using
      IsModularLattice.sup_inf_le_assoc_of_le aᶜ h

variable [IsOrthomodularLattice α] {a b : α}

theorem sup_compl_inf_of_le (h : a ≤ b) : a ⊔ aᶜ ⊓ b = b :=
  le_antisymm (sup_le h inf_le_right) (IsOrthomodularLattice.le_sup_compl_inf_of_le h)

end IsOrthomodularLattice
