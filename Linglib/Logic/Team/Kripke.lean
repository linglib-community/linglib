module

public import Linglib.Logic.Modal.Kripke

/-!
# Teams on Kripke models

BSML and modal dependence and inclusion logic evaluate formulas on a team of worlds of a Kripke
model (`Logic/Modal/Kripke.lean`), and InqML on the inquisitive models they induce. A pointed
team model, `ModalLogic.PointedTeam`, is a Kripke model with a team on it.

The file also states Aloni's two conditions on a successor function relative to a team, which
distinguish epistemic from deontic modals: indisputability, `Team.IsIndisputable`, that every
world of the team sees the same worlds, and state-basedness, `Team.IsStateBased`, that every
world of the team sees exactly the team ([aloni-2022] Definition 5).

## Implementation notes

Aloni's conditions are not closed under bisimulation ([aloni-2022] fn. 21): they are
[not invariant at any depth](##ModalLogic.not_boundedBisimInvariant_setOf_isIndisputable), so no
team logic defines them. [anttila-2021] Definition 3.3.1 (p. 46) restates them up to
bisimilarity of the successor sets.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal Logics
* [anttila-2025] Anttila, Not Nothing: Nonemptiness in Team Semantics
* [vaananen-2008] Väänänen, Modal Dependence Logic
-/

@[expose] public section

universe u

namespace ModalLogic

/-- A **pointed team model** is a Kripke model with a team on it, the pointed state model of
[anttila-2025] (p. 23); a class of them is a state property (Definition 2.3.9). -/
structure PointedTeam (Atom : Type*) where
  /-- The worlds of the model. -/
  World : Type u
  [decEq : DecidableEq World]
  /-- The model. -/
  model : KripkeModel World Atom
  /-- The team. -/
  team : Finset World

attribute [instance] PointedTeam.decEq

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
