module

public import Linglib.Logic.Team.BSML.Defs
public import Linglib.Logic.Team.Bisimulation
public import Linglib.Logic.Team.Closure
public import Linglib.Logic.Team.Definability

/-!
# Closure properties of BSML support

The teams supporting a BSML formula form a union-closed and order-convex family; when the
formula is `NE`-free they also include the empty team and are closed downward, so they are
determined by the singleton teams. Support and anti-support are moreover invariant under bounded
bisimulation. Anttila proves the closure properties, and Aloni, Anttila and Yang the invariance.
These are the properties for which BSML is expressively complete
(`BSML/ExpressiveCompleteness.lean`).

## Main results

* `supClosed_support`: support is union-closed.
* `support_empty_of_neFree`, `isLowerSet_support_of_neFree`: an `NE`-free formula is supported
  by the empty team and closed downward.
* `ordConnected_support`: support is order-convex.
* `isFlat_support_of_neFree`: an `NE`-free formula is flat.
* `invariant_eval`: `k`-bisimilar teams agree on every formula of modal depth at most `k`.

## Implementation notes

Negation swaps support and anti-support, so each property is proved for both polarities at once
by induction on the formula; each case is the lemma of its connective in `Team/Operations.lean`
or `Team/Bisimulation.lean`. Aloni, Anttila and Yang prove bisimulation invariance for support
of formulas in negation normal form; the joint induction needs no normal form.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal Logics
* [anttila-2025] Anttila, Not Nothing: Nonemptiness in Team Semantics
-/

@[expose] public section

namespace BSML

open ModalLogic (KripkeModel)

open Team

variable {W : Type*} [DecidableEq W] {Atom : Type*}

/-! ### Closure properties by induction over the connectives

Each case is the closure lemma of its connective from `Team/Operations.lean`, and
negation swaps the two polarities. -/

private theorem support_and_antiSupport_supClosed (φ : Formula Atom) (M : KripkeModel W Atom) :
    SupClosed {t | support M φ t} ∧ SupClosed {t | antiSupport M φ t} := by
  induction φ with
  | atom p => exact ⟨supClosed_flat _, supClosed_flat _⟩
  | ne => exact ⟨supClosed_ne, supClosed_singleton_empty⟩
  | neg ψ ih => exact ih.symm
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁.1.inter ih₂.1, ih₁.2.tensor ih₂.2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁.1.tensor ih₂.1, ih₁.2.inter ih₂.2⟩
  | poss ψ _ => exact ⟨supClosed_flat _, supClosed_flat _⟩

/-- BSML support is sup-closed ([anttila-2021] Proposition 2.2.8, second part). BSML's
    connective set lacks the global disjunction ⨼, so the union-closure
    obstruction is absent and all formulas satisfy the property. -/
theorem supClosed_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    SupClosed { t : Finset W | support M φ t } :=
  (support_and_antiSupport_supClosed φ M).1

private theorem support_and_antiSupport_empty_of_neFree
    (φ : Formula Atom) (hNE : φ.NEFree) (M : KripkeModel W Atom) :
    support M φ ∅ ∧ antiSupport M φ ∅ := by
  induction φ with
  | atom p => exact ⟨empty_mem_flat _, empty_mem_flat _⟩
  | ne => exact hNE.elim
  | neg ψ ih => exact (ih hNE).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨⟨(ih₁ hNE.1).1, (ih₂ hNE.2).1⟩, empty_mem_tensor (ih₁ hNE.1).2 (ih₂ hNE.2).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨empty_mem_tensor (ih₁ hNE.1).1 (ih₂ hNE.2).1, ⟨(ih₁ hNE.1).2, (ih₂ hNE.2).2⟩⟩
  | poss ψ _ => exact ⟨empty_mem_flat _, empty_mem_flat _⟩

theorem support_empty_of_neFree {φ : Formula Atom}
    (hNE : φ.NEFree) (M : KripkeModel W Atom) : support M φ ∅ :=
  (support_and_antiSupport_empty_of_neFree φ hNE M).1

private theorem support_and_antiSupport_isLowerSet_of_neFree
    (φ : Formula Atom) (hNE : φ.NEFree) (M : KripkeModel W Atom) :
    IsLowerSet {t | support M φ t} ∧ IsLowerSet {t | antiSupport M φ t} := by
  induction φ with
  | atom p => exact ⟨isLowerSet_flat _, isLowerSet_flat _⟩
  | ne => exact hNE.elim
  | neg ψ ih => exact (ih hNE).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hNE.1).1.inter (ih₂ hNE.2).1, (ih₁ hNE.1).2.tensor (ih₂ hNE.2).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hNE.1).1.tensor (ih₂ hNE.2).1, (ih₁ hNE.1).2.inter (ih₂ hNE.2).2⟩
  | poss ψ _ => exact ⟨isLowerSet_flat _, isLowerSet_flat _⟩

theorem isLowerSet_support_of_neFree {φ : Formula Atom}
    (hNE : φ.NEFree) (M : KripkeModel W Atom) :
    IsLowerSet { t : Finset W | support M φ t } :=
  (support_and_antiSupport_isLowerSet_of_neFree φ hNE M).1

/-- Support and anti-support are jointly order-convex. [anttila-2025] Proposition 3.3.6 (p. 82)
    proves convexity for BSML without its bilateral negation, which swaps the polarities, so here
    both are proved together. The split cases need union closure of the subformulas
    (`Set.OrdConnected.tensor`), since split disjunction preserves convexity only in a
    union-closed setting ([anttila-2025] Fact 3.2.7, p. 71, against Proposition 3.3.1, p. 79). -/
private theorem support_and_antiSupport_ordConnected
    (φ : Formula Atom) (M : KripkeModel W Atom) :
    Set.OrdConnected {t | support M φ t} ∧ Set.OrdConnected {t | antiSupport M φ t} := by
  induction φ with
  | atom p => exact ⟨ordConnected_flat _, ordConnected_flat _⟩
  | ne => exact ⟨ordConnected_ne, ordConnected_singleton_empty⟩
  | neg ψ ih => exact ih.symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨ih₁.1.inter ih₂.1, ih₁.2.tensor ih₂.2 (support_and_antiSupport_supClosed ψ₁ M).2
      (support_and_antiSupport_supClosed ψ₂ M).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨ih₁.1.tensor ih₂.1 (support_and_antiSupport_supClosed ψ₁ M).1
      (support_and_antiSupport_supClosed ψ₂ M).1, ih₁.2.inter ih₂.2⟩
  | poss ψ _ => exact ⟨ordConnected_flat _, ordConnected_flat _⟩

/-- BSML support is order-convex for every formula, `NE` included ([anttila-2025]
    Proposition 3.3.6 and the remark after Theorem 3.3.7, pp. 82–83), so a team between two
    supporting teams supports the formula too. With
    `supClosed_support`, this is the property for which BSML is expressively complete. -/
theorem ordConnected_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    Set.OrdConnected { t : Finset W | support M φ t } :=
  (support_and_antiSupport_ordConnected φ M).1

/-! ### Flatness corollary (Anttila 2.2.16) -/

/-- An `NE`-free BSML formula is flat ([anttila-2021] Proposition 2.2.16), by Anttila's
    Proposition 2.2.2 applied to the three closure properties above. -/
theorem isFlat_support_of_neFree {φ : Formula Atom}
    (hNE : φ.NEFree) (M : KripkeModel W Atom) :
    IsFlat { t : Finset W | support M φ t } :=
  isFlat_of_isLowerSet_supClosed_empty
    (isLowerSet_support_of_neFree hNE M)
    (supClosed_support M φ)
    (support_empty_of_neFree hNE M)

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

/-! ### Soundness for the closure cell (Definability bridge) -/

open Team in
/-- **The NE-free fragment of BSML defines flat properties** ([anttila-2021] Proposition
    2.2.16), the fragment being the subtype of `NE`-free formulas. `NE` is exactly what moves a
    formula off the flat properties into the convex, union-closed ones
    (`definableClass_support_subset` in `BSML/ExpressiveCompleteness.lean`). -/
theorem definableClass_support_neFree_subset (M : KripkeModel W Atom) :
    definableClass (fun φ : {φ : Formula Atom // φ.NEFree} ↦ support M φ.1) ⊆ {P | IsFlat P} :=
  definableClass_subset fun φ ↦ isFlat_support_of_neFree φ.2 M

end BSML
