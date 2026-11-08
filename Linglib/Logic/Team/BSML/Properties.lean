module

public import Linglib.Logic.Team.BSML.Classical
public import Linglib.Logic.Team.Bisimulation

/-!
# Closure properties of BSML support

This file proves that the teams supporting a BSML formula form a union-closed and order-convex
family, invariant under bounded bisimulation, and that those supporting an `NE`-free formula form
a flat one. These are the properties for which BSML and its `NE`-free fragment are expressively
complete (`BSML/ExpressiveCompleteness.lean`).

## Main results

* `den_induction`: every support and anti-support set lies in the closure of the flat
  properties, `NE` and `{∅}` under `∩` and `⊻`.
* `supClosed_support`: support is union-closed.
* `ordConnected_support`: support is order-convex.
* `isFlat_support_of_neFree`: an `NE`-free formula is flat.
* `invariant_den`: `k`-bisimilar teams agree on every formula of modal depth at most `k`.

## Implementation notes

The modalities define flat properties whatever their argument, so `den_induction` has no modal
case, and negation swaps the two polarities, so it proves a property of both at once. Anttila,
and Aloni, Anttila and Yang, derive the flatness of the `NE`-free fragment from its closure
properties, and from flatness that support is classical truth at every world of the team. Here
the order is reversed: that equation is `support_iff_forall_realize` in `BSML/Classical.lean`,
and flatness, downward closure and the empty-team property follow from it. Aloni, Anttila and
Yang prove bisimulation invariance for formulas in negation normal form; the joint induction
needs no normal form.

## References

* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal Logics
* [anttila-2025] Anttila, Not Nothing: Nonemptiness in Team Semantics
-/

public section

open scoped SetFamily

namespace BSML

open ModalLogic (KripkeModel)

open Team

variable {W : Type*} [DecidableEq W] {Atom : Type*}

/-! ### Union closure and convexity -/

/-- The support and anti-support sets of every formula lie in the closure of the flat team
properties, `NE` and `{∅}` under `∩` and `⊻`. -/
theorem den_induction {C : TeamProperty W → Prop} (flat : ∀ p, C (Team.flat p))
    (ne : C Team.ne) (empty : C {∅}) (inter : ∀ {P Q}, C P → C Q → C (P ∩ Q))
    (sups : ∀ {P Q}, C P → C Q → C (P ⊻ Q)) (M : KripkeModel W Atom)
    (φ : Formula Atom) : C (φ.den M).pro ∧ C (φ.den M).con := by
  induction φ with
  | atom p => exact ⟨flat _, flat _⟩
  | ne => exact ⟨ne, empty⟩
  | neg ψ ih => exact ih.symm
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨inter ih₁.1 ih₂.1, sups ih₁.2 ih₂.2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨sups ih₁.1 ih₂.1, inter ih₁.2 ih₂.2⟩
  | poss ψ _ => exact ⟨flat _, flat _⟩

/-- BSML support is union-closed ([anttila-2021] Proposition 2.2.8). -/
theorem supClosed_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    SupClosed {t | support M φ t} :=
  (den_induction supClosed_flat supClosed_ne supClosed_singleton_empty .inter .sups M φ).1

/-- BSML support is order-convex, `NE` included ([anttila-2025] Proposition 3.3.6 and the remark
after Theorem 3.3.7, pp. 82–83). -/
theorem ordConnected_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    {t | support M φ t}.OrdConnected :=
  (den_induction (C := fun P : TeamProperty W ↦ P.OrdConnected ∧ SupClosed P)
    (fun p ↦ ⟨ordConnected_flat p, supClosed_flat p⟩) ⟨ordConnected_ne, supClosed_ne⟩
    ⟨ordConnected_singleton_empty, supClosed_singleton_empty⟩
    (fun h₁ h₂ ↦ ⟨h₁.1.inter h₂.1, h₁.2.inter h₂.2⟩)
    (fun h₁ h₂ ↦ ⟨h₁.1.sups h₂.1 h₁.2 h₂.2, h₁.2.sups h₂.2⟩) M φ).1.1

/-! ### The `NE`-free fragment -/

variable {φ : Formula Atom}

/-- An `NE`-free BSML formula is flat ([anttila-2021] Corollary 2.2.9). -/
theorem isFlat_support_of_neFree (hNE : φ.NEFree) (M : KripkeModel W Atom) :
    IsFlat {t | support M φ t} :=
  fun _ ↦ by simp [support_iff_forall_realize hNE]

/-- An `NE`-free BSML formula is supported by the empty team ([anttila-2021] Proposition 2.2.8). -/
theorem support_empty_of_neFree (hNE : φ.NEFree) (M : KripkeModel W Atom) : support M φ ∅ :=
  (isFlat_support_of_neFree hNE M).empty_mem

/-- An `NE`-free BSML formula is downward closed ([anttila-2021] Proposition 2.2.8). -/
theorem isLowerSet_support_of_neFree (hNE : φ.NEFree) (M : KripkeModel W Atom) :
    IsLowerSet {t | support M φ t} :=
  (isFlat_support_of_neFree hNE M).isLowerSet

/-! ### Bisimulation invariance -/

section Bisimulation

open ModalLogic (WorldBisim)

variable {W' : Type*} [DecidableEq W'] {M : KripkeModel W Atom} {M' : KripkeModel W' Atom}

/-- Teams that are `k`-bisimilar agree on every formula of modal depth at most `k`, in both
polarities ([aloni-anttila-yang-2024] Theorem 3.8). -/
theorem invariant_den {k : ℕ} (φ : Formula Atom) (hd : φ.modalDepth ≤ k) :
    Invariant (WorldBisim k M · M' ·) (φ.den M).pro (φ.den M').pro ∧
      Invariant (WorldBisim k M · M' ·) (φ.den M).con (φ.den M').con := by
  induction φ generalizing k with
  | atom p => exact ⟨invariant_flat fun _ _ h ↦ h.val_iff p,
      invariant_flat fun _ _ h ↦ not_congr (h.val_iff p)⟩
  | ne => exact ⟨invariant_ne, invariant_singleton_empty⟩
  | neg ψ ih => exact (ih hd).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    exact ⟨(ih₁ hd₁).1.inter (ih₂ hd₂).1, (ih₁ hd₁).2.sups (ih₂ hd₂).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    exact ⟨(ih₁ hd₁).1.sups (ih₂ hd₂).1, (ih₁ hd₁).2.inter (ih₂ hd₂).2⟩
  | poss ψ ih =>
    obtain _ | k := k
    · exact absurd hd (Nat.not_succ_le_zero _)
    have ih := ih (Nat.le_of_succ_le_succ hd)
    exact ⟨ih.1.poss fun _ _ h ↦ h.2, ih.2.nec fun _ _ h ↦ h.2⟩

end Bisimulation

end BSML
