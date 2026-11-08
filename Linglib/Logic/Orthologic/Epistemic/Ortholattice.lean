module

public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Logic.Function.Iterate
public import Linglib.Core.Order.Ortholattice

/-!
# Epistemic ortholattices

This file defines epistemic ortholattices, Holliday and Mandelkern's algebraic semantics for
`must` and `might`. A modal ortholattice is an ortholattice with a necessity operator `□`
preserving `⊓` and `⊤`, and its possibility operator `◇a = ¬□¬a` preserves `⊔` and `⊥`. It is
*epistemic* when `□a ≤ a` (T) and Wittgenstein's Law `¬a ∧ ◇a = 0` holds, which makes "`p`,
but it might be that not `p`" a contradiction. Over T the law [says that `a = 0` whenever
`□a = 0`](##Orthologic.wittgensteinLaw_iff_eq_bot), and it makes [every `a ∧ ◇ⁿ¬a`
zero](##Orthologic.IsEpistemic.disjoint_diamondHom_iterate). The law is what forces ortholattices
on the account: [when `ᶜ` is a pseudocomplement](##Orthologic.IsEpistemic.eq_id), as in a Boolean
algebra, it makes `□` the identity.

## Implementation notes

The paper's modal ortholattice is not a new structure: `□` is a bundled `InfTopHom L L`, since
one lattice carries many modalities, and `IsEpistemic box` is the `Prop` that it is factive and
satisfies the law. The frame semantics producing epistemic ortholattices is
`Logic/Orthologic/Epistemic/Compatibility.lean`, and the logic they characterize is
`Logic/Orthologic/Epistemic/Basic.lean`.

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

theorem diamondHom_iterate_compl (n : ℕ) (a : L) : (diamondHom box)^[n] aᶜ = (box^[n] a)ᶜ :=
  (Function.Semiconj.iterate_right (f := (·ᶜ)) (fun b ↦ by
    rw [diamondHom_apply, InvolutiveCompl.compl_compl]) n a).symm

/-- With 4, the principle `a ≤ □◇a` yields 5, `◇a ≤ □◇a` ([holliday-mandelkern-2024] Definition 3.19
and the proof of Theorem 5.7.3). -/
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

/-- Wittgenstein's Law is equivalent to `a ∧ ◇¬a = 0` ([holliday-mandelkern-2024] after Definition
3.18). -/
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

variable (box) in
/-- `box` makes `L` an *epistemic ortholattice* when it is factive, `□a ≤ a` (T), and satisfies
Wittgenstein's Law ([holliday-mandelkern-2024] Definitions 3.17 and 3.18). -/
structure IsEpistemic : Prop where
  apply_le (a : L) : box a ≤ a
  wittgensteinLaw : WittgensteinLaw box

/-- Over T, Wittgenstein's Law holds iff `□a = 0` implies `a = 0` ([holliday-mandelkern-2024] after
Lemma 3.25). -/
theorem wittgensteinLaw_iff_eq_bot [IsOrtholattice L] (hT : ∀ a, box a ≤ a) :
    WittgensteinLaw box ↔ ∀ a, box a = ⊥ → a = ⊥ := by
  refine ⟨fun hW _ ↦ hW.eq_bot_of_box_eq_bot, fun h ↦ wittgensteinLaw_iff.mpr fun a ↦ ?_⟩
  refine disjoint_iff.mpr (h _ (le_bot_iff.mp ?_))
  rw [map_inf]
  exact ((IsOrtholattice.disjoint_compl_right (box a)).mono_right (hT _)).le_bot

namespace IsEpistemic

variable [IsOrtholattice L] (h : IsEpistemic box)
include h

/-- In an epistemic ortholattice `a ∧ ¬□ⁿa = 0` for every `n`, by induction from
`eq_bot_of_box_eq_bot`. -/
theorem disjoint_compl_box_iterate : ∀ n (a : L), Disjoint a (box^[n] a)ᶜ
  | 0, a => IsOrtholattice.disjoint_compl_right a
  | n + 1, a => by
    rw [Function.iterate_succ_apply, disjoint_iff]
    refine h.wittgensteinLaw.eq_bot_of_box_eq_bot (le_bot_iff.mp ?_)
    rw [map_inf]
    exact ((disjoint_compl_box_iterate n (box a)).mono_right (h.apply_le _)).le_bot

/-- In an epistemic ortholattice the generalized Wittgenstein sentences `a ∧ ◇ⁿ¬a` are
contradictions ([holliday-mandelkern-2024] Fact 3.28). -/
theorem disjoint_diamondHom_iterate (n : ℕ) (a : L) :
    Disjoint a ((diamondHom box)^[n] aᶜ) := by
  rw [diamondHom_iterate_compl]
  exact h.disjoint_compl_box_iterate n a

end IsEpistemic

section Pseudocomplement

/-! ### The collapse under pseudocomplementation

The hypothesis `hp` says that `ᶜ` is a pseudocomplement, `a ⊓ b = ⊥ → b ≤ aᶜ`. It holds in every
Boolean algebra (`Disjoint.le_compl_left`), and in an ortholattice it is
[equivalent to distributivity](##IsOrtholattice.inf_sup_le_iff_le_compl_of_disjoint). -/

variable (hp : ∀ a b : L, Disjoint a b → b ≤ aᶜ)
include hp

/-- When `ᶜ` is a pseudocomplement, Wittgenstein's Law says that `◇¬a` entails `¬a`
([holliday-mandelkern-2024] §1). -/
theorem wittgensteinLaw_iff_diamondHom_compl_le [IsOrtholattice L] :
    WittgensteinLaw box ↔ ∀ a, diamondHom box aᶜ ≤ aᶜ := by
  rw [wittgensteinLaw_iff]
  refine forall_congr' fun a ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa only [diamondHom_apply, InvolutiveCompl.compl_compl] using hp _ _ h
  · simpa only [diamondHom_apply, InvolutiveCompl.compl_compl] using
      (IsOrtholattice.disjoint_compl_right a).mono_right h

/-- When `ᶜ` is a pseudocomplement, an epistemic `□` is the identity, so a Boolean algebra has no
non-trivial epistemic modality. -/
theorem IsEpistemic.eq_id (h : IsEpistemic box) : box = InfTopHom.id L :=
  InfTopHom.ext fun a ↦ (h.apply_le a).antisymm <|
    InvolutiveCompl.compl_le_compl_iff_le.mp (hp _ _ (h.wittgensteinLaw.disjoint_compl_box a))

end Pseudocomplement

end Orthologic
