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

* `eval_induction`: every support and anti-support set lies in the closure of the flat
  properties, `NE` and `{∅}` under `∩` and tensor.
* `supClosed_support`: support is union-closed.
* `ordConnected_support`: support is order-convex.
* `isFlat_support_of_neFree`: an `NE`-free formula is flat.
* `invariant_eval`: `k`-bisimilar teams agree on every formula of modal depth at most `k`.

## Implementation notes

The modalities define flat properties whatever their argument, so `eval_induction` has no modal
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

@[expose] public section

namespace BSML

open ModalLogic (KripkeModel)

open Team

variable {W : Type*} [DecidableEq W] {Atom : Type*}

/-! ### Union closure and convexity -/

/-- Every support and anti-support set lies in the closure of the flat team properties, `NE` and
`{∅}` under `∩` and tensor. -/
theorem eval_induction {C : TeamProperty W → Prop} (flat : ∀ p, C (Team.flat p))
    (ne : C Team.ne) (empty : C {∅}) (inter : ∀ {P Q}, C P → C Q → C (P ∩ Q))
    (tensor : ∀ {P Q}, C P → C Q → C (Team.tensor P Q)) (M : KripkeModel W Atom) (b : Bool)
    (φ : Formula Atom) : C {t | eval M b φ t} := by
  induction φ generalizing b with
  | atom p => cases b <;> exact flat _
  | ne => cases b; exacts [empty, ne]
  | neg ψ ih => cases b <;> exact ih _
  | conj ψ₁ ψ₂ ih₁ ih₂ => cases b; exacts [tensor (ih₁ _) (ih₂ _), inter (ih₁ _) (ih₂ _)]
  | disj ψ₁ ψ₂ ih₁ ih₂ => cases b; exacts [inter (ih₁ _) (ih₂ _), tensor (ih₁ _) (ih₂ _)]
  | poss ψ _ => cases b <;> exact flat _

/-- BSML support is union-closed ([anttila-2021] Proposition 2.2.8). -/
theorem supClosed_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    SupClosed {t | support M φ t} :=
  eval_induction supClosed_flat supClosed_ne supClosed_singleton_empty .inter .tensor M true φ

/-- BSML support is order-convex, `NE` included ([anttila-2025] Proposition 3.3.6 and the remark
after Theorem 3.3.7, pp. 82–83). -/
theorem ordConnected_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    {t | support M φ t}.OrdConnected :=
  (eval_induction (C := fun P ↦ P.OrdConnected ∧ SupClosed P)
    (fun p ↦ ⟨ordConnected_flat p, supClosed_flat p⟩) ⟨ordConnected_ne, supClosed_ne⟩
    ⟨ordConnected_singleton_empty, supClosed_singleton_empty⟩
    (fun h₁ h₂ ↦ ⟨h₁.1.inter h₂.1, h₁.2.inter h₂.2⟩)
    (fun h₁ h₂ ↦ ⟨h₁.1.tensor h₂.1 h₁.2 h₂.2, h₁.2.tensor h₂.2⟩) M true φ).1

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
theorem invariant_eval {k : ℕ} (φ : Formula Atom) (hd : φ.modalDepth ≤ k) (b : Bool) :
    Invariant (WorldBisim k M · M' ·) {t | eval M b φ t} {t | eval M' b φ t} := by
  induction φ generalizing k b with
  | atom p =>
    cases b
    · exact invariant_flat fun _ _ h ↦ not_congr (h.val_iff p)
    · exact invariant_flat fun _ _ h ↦ h.val_iff p
  | ne => cases b; exacts [invariant_singleton_empty, invariant_ne]
  | neg ψ ih => cases b <;> exact ih hd _
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    cases b; exacts [(ih₁ hd₁ _).tensor (ih₂ hd₂ _), (ih₁ hd₁ _).inter (ih₂ hd₂ _)]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    cases b; exacts [(ih₁ hd₁ _).inter (ih₂ hd₂ _), (ih₁ hd₁ _).tensor (ih₂ hd₂ _)]
  | poss ψ ih =>
    obtain _ | k := k
    · exact absurd hd (Nat.not_succ_le_zero _)
    have ih := ih (Nat.le_of_succ_le_succ hd)
    cases b; exacts [(ih _).nec fun _ _ h ↦ h.2, (ih _).poss fun _ _ h ↦ h.2]

end Bisimulation

end BSML
