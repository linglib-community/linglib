module

public import Mathlib.Data.Finset.Basic
public import Linglib.Logic.Modal.Defs

/-!
# Kripke models

A Kripke model gives each world the finite set of worlds it accesses and each atom the worlds
at which it is true. The team-semantic modal logics (BSML, QBSML, modal dependence and inclusion
logic, InqML) evaluate formulas on these models. `KripkeModel.accessible` reads the successor
sets as the relation that `□` and `◇` of `Logic/Modal/Defs.lean` take.

The file also states Aloni's two conditions on the accessibility relation relative to a team,
which distinguish epistemic from deontic modals: indisputability, that every world of the team
sees the same worlds, and state-basedness, that every world of the team sees exactly the team.

## Main definitions

* `ModalLogic.KripkeModel`, with the accessibility relation `KripkeModel.accessible`.
* `Team.IsIndisputable`, `Team.IsStateBased`: the conditions of [aloni-2022] Definition 5.

## Implementation notes

The sources take any relation `R ⊆ W × W` and a valuation `V : X → ℘(W)`
([aloni-anttila-yang-2024] Definition 2.2). Successor sets here are `Finset`s, since the team
clauses evaluate subformulas on `R[w]` as a team; frames are therefore image-finite. The
valuation is `Prop`-valued, and decision procedures for support take `[DecidableRel M.val]`.
Aloni's conditions are not closed under bisimulation ([aloni-2022] fn. 21); [anttila-2021]
Definition 3.3.1 (p. 46) restates them up to bisimilarity of the successor sets.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal Logics
* [vaananen-2008] Väänänen, Modal Dependence Logic
-/

@[expose] public section

namespace ModalLogic

/-- A **Kripke model** over worlds `W` and atoms `Atom` has successor sets and a valuation. -/
structure KripkeModel (W : Type*) (Atom : Type*) where
  /-- `access w` is the set of worlds accessible from `w`. -/
  access : W → Finset W
  /-- `val p w` says that the atom `p` is true at the world `w`. -/
  val : Atom → W → Prop

variable {W : Type*} {Atom : Type*}

/-- The disjoint union of two Kripke models. -/
def KripkeModel.sum {W' : Type*} (M : KripkeModel W Atom) (M' : KripkeModel W' Atom) :
    KripkeModel (W ⊕ W') Atom where
  access := Sum.elim (fun w ↦ (M.access w).map .inl) (fun w ↦ (M'.access w).map .inr)
  val p := Sum.elim (M.val p) (M'.val p)

open SetRel in
/-- In the accessibility relation of `M`, `v` is accessible from `w` when `v ∈ M.access w`.
This is the relation that `□` and `◇` of `Logic/Modal/Defs.lean` take. -/
def KripkeModel.accessible (M : KripkeModel W Atom) : SetRel W W :=
  .ofSuccessors fun w ↦ ↑(M.access w)

open SetRel in
@[simp] theorem KripkeModel.mem_accessible {M : KripkeModel W Atom} {w v : W} :
    w ~[M.accessible] v ↔ v ∈ M.access w := .rfl

open SetRel in
instance [DecidableEq W] (M : KripkeModel W Atom) (w v : W) : Decidable (w ~[M.accessible] v) :=
  inferInstanceAs (Decidable (v ∈ M.access w))

end ModalLogic

/-! ### Conditions on accessibility relative to a team -/

namespace Team

variable {W : Type*}

/-- `R` is **indisputable** on the team `t` when all worlds of `t` see the same worlds
([aloni-2022] Definition 5). -/
def IsIndisputable (R : W → Finset W) (t : Finset W) : Prop :=
  ∀ w₁ ∈ t, ∀ w₂ ∈ t, R w₁ = R w₂

/-- `R` is **state-based** on the team `t` when every world of `t` sees exactly `t`
([aloni-2022] Definition 5). -/
def IsStateBased (R : W → Finset W) (t : Finset W) : Prop :=
  ∀ w ∈ t, R w = t

theorem IsStateBased.isIndisputable {R : W → Finset W} {t : Finset W}
    (h : IsStateBased R t) : IsIndisputable R t :=
  fun w₁ hw₁ w₂ hw₂ ↦ (h w₁ hw₁).trans (h w₂ hw₂).symm

instance [DecidableEq W] (R : W → Finset W) (t : Finset W) : Decidable (IsIndisputable R t) :=
  inferInstanceAs (Decidable (∀ w₁ ∈ t, ∀ w₂ ∈ t, _))

instance [DecidableEq W] (R : W → Finset W) (t : Finset W) : Decidable (IsStateBased R t) :=
  inferInstanceAs (Decidable (∀ w ∈ t, _))

end Team
