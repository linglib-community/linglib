module

public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Logic.Function.Iterate
public import Linglib.Core.Order.Ortholattice

/-!
# Epistemic ortholattices

This file defines epistemic ortholattices, Holliday and Mandelkern's algebraic semantics for
`must` and `might`. A modal ortholattice is an ortholattice with a necessity operator `□`
preserving `⊓` and `⊤`, and its possibility operator `◇a = ¬□¬a` preserves `⊔` and `⊥`. It is
*T* when `□a ≤ a`, and *epistemic* when it is T and satisfies Wittgenstein's Law `¬a ∧ ◇a = 0`,
which makes "`p`, but it might be that not `p`" a contradiction.

The law is what forces ortholattices on the account. In a Boolean algebra it makes `◇¬a` entail
`¬a`, and with T it makes `□` the identity. In an ortholattice, where `a ⊓ b = ⊥` need not give
`b ≤ aᶜ`, it is compatible with a non-trivial `□`.

## Main definitions

* `Orthologic.diamondHom`: `◇a = ¬□¬a` as a map preserving `⊔` and `⊥`.
* `Orthologic.WittgensteinLaw`: `¬a ∧ ◇a = 0`.

## Main results

* `Orthologic.wittgensteinLaw_iff`: the law in the form `a ∧ ◇¬a = 0`.
* `Orthologic.wittgensteinLaw_iff_eq_bot`: with T, the law holds iff `□a = 0` implies `a = 0`.
* `Orthologic.WittgensteinLaw.disjoint_diamondHom_iterate`: with T, `a ∧ ◇ⁿ¬a = 0` for every `n`.
* `Orthologic.diamondHom_le_box_diamondHom`: 4 and `a ≤ □◇a` give 5, `◇a ≤ □◇a`.
* `Orthologic.wittgensteinLaw_iff_diamondHom_compl_le`, `Orthologic.WittgensteinLaw.eq_id`: the
  collapse when `ᶜ` is a pseudocomplement, as in a Boolean algebra.

## Implementation notes

The paper's modal ortholattice is not a new structure: `□` is a bundled `InfTopHom L L`, since
one lattice carries many modalities, and T is the hypothesis `∀ a, box a ≤ a`. An epistemic
ortholattice is the conjunction of T and `WittgensteinLaw`. The frame semantics producing
epistemic ortholattices is `Logic/Orthologic/ModalFrame.lean`, and the logic they characterize
is `Logic/Orthologic/EpistemicOrthologic.lean`.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

namespace Orthologic

variable {L : Type*} [Lattice L] [BoundedOrder L] [InvolutiveCompl L]

/-- `diamondHom box` is the possibility operator `◇a = ¬□¬a` of `box`, which preserves joins
and `⊥` ([holliday-mandelkern-2024] Definition 3.15 and Lemma 3.16). -/
def diamondHom (box : InfTopHom L L) : SupBotHom L L where
  toFun a := (box aᶜ)ᶜ
  map_sup' a b := by simp only [InvolutiveCompl.compl_sup, map_inf, InvolutiveCompl.compl_inf]
  map_bot' := by simp only [InvolutiveCompl.compl_bot, map_top, InvolutiveCompl.compl_top]

variable {box : InfTopHom L L}

@[simp] theorem diamondHom_apply (a : L) : diamondHom box a = (box aᶜ)ᶜ := rfl

theorem diamondHom_iterate_compl (n : ℕ) (a : L) : (diamondHom box)^[n] aᶜ = (box^[n] a)ᶜ := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, diamondHom_apply,
      InvolutiveCompl.compl_compl, ih]

/-- With 4, `□a ≤ □□a`, the principle `a ≤ □◇a` yields 5, `◇a ≤ □◇a`, so that `□` makes an
*S5* modal ortholattice when it is also T ([holliday-mandelkern-2024] Definition 3.19 and the
proof of Theorem 5.7.3). -/
theorem diamondHom_le_box_diamondHom (h4 : ∀ a, box a ≤ box (box a))
    (hB : ∀ a, a ≤ box (diamondHom box a)) (a : L) :
    diamondHom box a ≤ box (diamondHom box a) :=
  (hB _).trans <| OrderHomClass.mono box <| by
    simpa only [diamondHom_apply, InvolutiveCompl.compl_compl,
      InvolutiveCompl.compl_le_compl_iff_le] using h4 aᶜ

variable (box) in
/-- Wittgenstein's Law `¬a ∧ ◇a = 0` makes "`p` is not the case but might be" a contradiction.
With T it makes an ortholattice with `□` an *epistemic ortholattice*
([holliday-mandelkern-2024] Definition 3.18). -/
def WittgensteinLaw : Prop :=
  ∀ a, Disjoint aᶜ (diamondHom box a)

/-- Wittgenstein's Law is equivalent by involution to its form `a ∧ ◇¬a = 0`, "`p`, but it
might be that not `p`" ([holliday-mandelkern-2024] after Definition 3.18). -/
theorem wittgensteinLaw_iff : WittgensteinLaw box ↔ ∀ a, Disjoint a (box a)ᶜ :=
  InvolutiveCompl.compl_surjective.forall.trans <| by
    simp only [diamondHom_apply, InvolutiveCompl.compl_compl]

namespace WittgensteinLaw

variable (hW : WittgensteinLaw box)
include hW

theorem disjoint_compl_box (a : L) : Disjoint a (box a)ᶜ :=
  wittgensteinLaw_iff.mp hW a

/-- A proposition whose necessity is contradictory is itself contradictory
([holliday-mandelkern-2024] Lemma 3.25, algebraically). -/
theorem eq_bot_of_box_eq_bot {a : L} (h : box a = ⊥) : a = ⊥ := by
  simpa [h] using hW.disjoint_compl_box a

end WittgensteinLaw

section T

variable [IsOrtholattice L] (hT : ∀ a, box a ≤ a)
include hT

/-- Over T, Wittgenstein's Law is equivalent to the principle of Lemma 3.25 that a proposition
whose necessity is contradictory is itself contradictory ([holliday-mandelkern-2024] after
Lemma 3.25). -/
theorem wittgensteinLaw_iff_eq_bot : WittgensteinLaw box ↔ ∀ a, box a = ⊥ → a = ⊥ := by
  refine ⟨fun hW _ ↦ hW.eq_bot_of_box_eq_bot, fun h ↦ wittgensteinLaw_iff.mpr fun a ↦ ?_⟩
  refine disjoint_iff.mpr (h _ (le_bot_iff.mp ?_))
  rw [map_inf]
  exact ((IsOrtholattice.disjoint_compl_right (box a)).mono_right (hT _)).le_bot

/-- Generalized Wittgenstein sentences are contradictions, since with T `a ∧ ◇ⁿ¬a = 0` for every
`n`, here in the form `a ⊓ ¬□ⁿa = ⊥` ([holliday-mandelkern-2024] Fact 3.28, algebraically). -/
theorem WittgensteinLaw.disjoint_compl_box_iterate (hW : WittgensteinLaw box) :
    ∀ n (a : L), Disjoint a (box^[n] a)ᶜ
  | 0, a => IsOrtholattice.disjoint_compl_right a
  | n + 1, a => by
    rw [Function.iterate_succ_apply, disjoint_iff]
    refine hW.eq_bot_of_box_eq_bot (le_bot_iff.mp ?_)
    rw [map_inf]
    exact ((disjoint_compl_box_iterate hW n (box a)).mono_right (hT _)).le_bot

/-- This is Fact 3.28 in the paper's form `a ∧ ◇ⁿ¬a = 0`. -/
theorem WittgensteinLaw.disjoint_diamondHom_iterate (hW : WittgensteinLaw box) (n : ℕ) (a : L) :
    Disjoint a ((diamondHom box)^[n] aᶜ) := by
  rw [diamondHom_iterate_compl]
  exact hW.disjoint_compl_box_iterate hT n a

end T

section Pseudocomplement

/-! ### The collapse under pseudocomplementation

The hypothesis `hp` says that `ᶜ` is a pseudocomplement, `a ⊓ b = ⊥ → b ≤ aᶜ`. It holds in every
Boolean algebra (`Disjoint.le_compl_left`), and in an ortholattice it is equivalent to
distributivity ([holliday-mandelkern-2024] Proposition 3.7). -/

variable (hp : ∀ a b : L, Disjoint a b → b ≤ aᶜ)
include hp

/-- When `ᶜ` is a pseudocomplement, as in a Boolean algebra, Wittgenstein's Law says that `◇¬a`
entails `¬a`, so treating `p ∧ ◇¬p` as a contradiction collapses `might`
([holliday-mandelkern-2024] §1). -/
theorem wittgensteinLaw_iff_diamondHom_compl_le [IsOrtholattice L] :
    WittgensteinLaw box ↔ ∀ a, diamondHom box aᶜ ≤ aᶜ := by
  rw [wittgensteinLaw_iff]
  refine forall_congr' fun a ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa only [diamondHom_apply, InvolutiveCompl.compl_compl] using hp _ _ h
  · simpa only [diamondHom_apply, InvolutiveCompl.compl_compl] using
      (IsOrtholattice.disjoint_compl_right a).mono_right h

/-- When `ᶜ` is a pseudocomplement, with T Wittgenstein's Law makes `□` the identity, so a Boolean
algebra has no non-trivial epistemic modality. -/
theorem WittgensteinLaw.eq_id (hW : WittgensteinLaw box) (hT : ∀ a, box a ≤ a) :
    box = InfTopHom.id L :=
  InfTopHom.ext fun a ↦ (hT a).antisymm <|
    InvolutiveCompl.compl_le_compl_iff_le.mp (hp _ _ (hW.disjoint_compl_box a))

end Pseudocomplement

end Orthologic
