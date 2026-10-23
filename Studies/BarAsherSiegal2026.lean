module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Causation.CausalModel.Dependence
public import Linglib.Core.Relation.ReflTransGen

/-!
# Bar-Asher Siegal 2026: causation and causal relations

A review of how natural language encodes causation, from causative constructions and
conditionals to discourse coherence and the progressive, arguing that language is evidence
for the architecture of causal cognition. Its central proposal takes causal knowledge to be a
structural equation model in which several sets of conditions are each sufficient for an
effect: the door of Figure 1 opens when the handle is turned with the lock off, or when the
circuit is closed with the power on and the lock off. Causative constructions then differ in
which condition they may select as the cause. A change-of-state verb selects the temporally
final condition of a sufficient set, *cause* selects any of its conditions, and both select
only from the one sufficient set completed in the world of evaluation. Fodor's entailment from
*Sam opened the door* to *Sam caused the door to open* follows, its converse fails, and when
two sufficient sets are completed at once neither construction applies.

## Implementation notes

The door is a causal model whose exogenous variables (handle, lock, power, button) read the
context, and situations are observations. Sufficient sets and the two selection constraints are
stated over the Kleene development of an observation (`CausalModel.Forced`), after
[baglini-bar-asher-siegal-2025].

## References

* [bar-asher-siegal-2026]
* [baglini-bar-asher-siegal-2025]
* [fodor-1970]
-/

@[expose] public section

namespace BarAsherSiegal2026

open CausalModel

/-! ### Sufficient sets and selection -/

section Selection

variable {U W : Type*} {α : W → Type*} [DecidableEq W] (M : CausalModel U W α) [M.IsAcyclic]

/-- A sufficient set for `effect = xE` is a situation not settling the effect that forces it. -/
def IsSufficientSet (S : ∀ v, Flat (α v)) (effect : W) (xE : α effect) : Prop :=
  S effect = ⊥ ∧ M.Forced S effect xE

/-- A sufficient set each of whose conditions is necessary within it. -/
def IsMinimalSufficientSet (S : ∀ v, Flat (α v)) (effect : W) (xE : α effect) : Prop :=
  IsSufficientSet M S effect xE ∧ ∀ v, S v ≠ ⊥ → ¬ M.Forced (Function.update S v ⊥) effect xE

/-- `S` is the only minimal sufficient set completed in the world `w`. -/
def IsTheCompletedSet (w S : ∀ v, Flat (α v)) (effect : W) (xE : α effect) : Prop :=
  S ≤ w ∧ IsMinimalSufficientSet M S effect xE ∧
    ∀ S', S' ≤ w → IsMinimalSufficientSet M S' effect xE → S' = S

/-- The verb *cause* selects any condition of the completed sufficient set. -/
def SelectsMember (w : ∀ v, Flat (α v)) (c effect : W) (xE : α effect) : Prop :=
  ∃ S, IsTheCompletedSet M w S effect xE ∧ S c ≠ ⊥

/-- A change-of-state verb selects the temporally final condition of the completed sufficient
set, `time` ordering the world's realizations. -/
def SelectsFinal (w : ∀ v, Flat (α v)) (time : W → ℕ) (c effect : W) (xE : α effect) : Prop :=
  ∃ S, IsTheCompletedSet M w S effect xE ∧ S c ≠ ⊥ ∧ ∀ v, S v ≠ ⊥ → time v ≤ time c

variable {M} {effect : W} {xE : α effect}

theorem SelectsFinal.selectsMember {w : ∀ v, Flat (α v)} {time : W → ℕ} {c : W}
    (h : SelectsFinal M w time c effect xE) : SelectsMember M w c effect xE :=
  let ⟨S, hS, hc, _⟩ := h; ⟨S, hS, hc⟩

theorem not_selectsMember_of_two {w S₁ S₂ : ∀ v, Flat (α v)} {c : W}
    (h₁ : IsMinimalSufficientSet M S₁ effect xE) (h₂ : IsMinimalSufficientSet M S₂ effect xE)
    (hne : S₁ ≠ S₂) (hw₁ : S₁ ≤ w) (hw₂ : S₂ ≤ w) : ¬ SelectsMember M w c effect xE :=
  fun ⟨_, ⟨_, _, huniq⟩, _⟩ ↦ hne ((huniq S₁ hw₁ h₁).trans (huniq S₂ hw₂ h₂).symm)

section Decidable

variable [Fintype U] [Inhabited U] [∀ v, Inhabited (α v)] [∀ v, DecidableEq (α v)]
  [∀ v, Fintype (α v)] [Fintype W] [DecidableRel M.graph.Adj]

instance (S : ∀ v, Flat (α v)) : Decidable (IsSufficientSet M S effect xE) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (S : ∀ v, Flat (α v)) : Decidable (IsMinimalSufficientSet M S effect xE) :=
  haveI : ∀ v, Decidable (S v ≠ ⊥ → ¬ M.Forced (Function.update S v ⊥) effect xE) :=
    fun _ ↦ inferInstance
  inferInstanceAs (Decidable (_ ∧ _))

instance (w S : ∀ v, Flat (α v)) : Decidable (IsTheCompletedSet M w S effect xE) :=
  letI := fintypePartialAssignment (α := α)
  haveI : DecidablePred fun S' ↦ S' ≤ w → IsMinimalSufficientSet M S' effect xE → S' = S :=
    fun _ ↦ inferInstance
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (w : ∀ v, Flat (α v)) (c : W) : Decidable (SelectsMember M w c effect xE) :=
  letI := fintypePartialAssignment (α := α)
  haveI : DecidablePred fun S ↦ IsTheCompletedSet M w S effect xE ∧ S c ≠ ⊥ :=
    fun _ ↦ inferInstance
  inferInstanceAs (Decidable (∃ _, _))

instance (w : ∀ v, Flat (α v)) (time : W → ℕ) (c : W) :
    Decidable (SelectsFinal M w time c effect xE) :=
  letI := fintypePartialAssignment (α := α)
  haveI : DecidablePred fun S ↦ IsTheCompletedSet M w S effect xE ∧ S c ≠ ⊥ ∧
      ∀ v, S v ≠ ⊥ → time v ≤ time c := fun _ ↦ inferInstance
  inferInstanceAs (Decidable (∃ _, _))

end Decidable

end Selection

/-! ### The door of Figure 1 -/

/-- The variables of Figure 1. -/
inductive V | handle | lock | circuit | electricity | button | doorOpens
  deriving DecidableEq, Fintype, Repr

/-- The button closes the circuit; handle, lock, circuit and power bear on the door. -/
def edges : Finset (V × V) :=
  {(.button, .circuit), (.handle, .doorOpens), (.lock, .doorOpens), (.circuit, .doorOpens),
    (.electricity, .doorOpens)}

/-- The context settles the handle, the lock, the power, and the button. -/
structure Context where
  handle : Bool
  lock : Bool
  electricity : Bool
  button : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- The structural entailments G, H and I: the circuit closes when the button is pressed, and
the door opens manually (handle on, lock off) or automatically (circuit and power on, lock
off). -/
def model : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn
    | .handle => fun u _ ↦ u.handle
    | .lock => fun u _ ↦ u.lock
    | .electricity => fun u _ ↦ u.electricity
    | .button => fun u _ ↦ u.button
    | .circuit => fun _ x ↦ x .button
    | .doorOpens => fun _ x ↦
        (x .handle && !x .lock) || (x .circuit && x .electricity && !x .lock)

instance : DecidableRel model.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : model.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- Sufficient set I: handle on, lock off. -/
def manual : V → Flat Bool := [.handle ← true, .lock ← false]

/-- Sufficient set H: circuit and power on, lock off. -/
def automatic : V → Flat Bool := [.circuit ← true, .electricity ← true, .lock ← false]

/-- The world in which the handle is turned on an unlocked, unpowered door. -/
def handleWorld : V → Flat Bool :=
  [.handle ← true, .lock ← false, .button ← false, .electricity ← false, .circuit ← false,
    .doorOpens ← true]

/-- The overdetermined world: handle turned and button pressed on a powered, unlocked door. -/
def bothWorld : V → Flat Bool :=
  [.handle ← true, .lock ← false, .button ← true, .electricity ← true, .circuit ← true,
    .doorOpens ← true]

/-- The lock was disengaged first, the handle turned last. -/
def time : V → ℕ | .lock => 0 | .handle => 2 | _ => 1

theorem manual_minimal : IsMinimalSufficientSet model manual .doorOpens true := by
  decide +kernel

theorem automatic_minimal : IsMinimalSufficientSet model automatic .doorOpens true := by
  decide +kernel

theorem handle_selectsFinal : SelectsFinal model handleWorld time .handle .doorOpens true := by
  decide +kernel

theorem handle_selectsMember : SelectsMember model handleWorld .handle .doorOpens true :=
  handle_selectsFinal.selectsMember

theorem lock_selectsMember : SelectsMember model handleWorld .lock .doorOpens true := by
  decide +kernel

theorem lock_not_selectsFinal : ¬ SelectsFinal model handleWorld time .lock .doorOpens true := by
  decide +kernel

theorem overdetermined : ¬ SelectsMember model bothWorld .handle .doorOpens true :=
  not_selectsMember_of_two manual_minimal automatic_minimal (by decide) (by decide) (by decide)

end BarAsherSiegal2026
