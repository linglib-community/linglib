module

public import Linglib.Semantics.Dynamic.DRS.Indexed
public import Mathlib.Data.Fin.VecNotation

/-!
# Kamp, van Genabith and Reyle (2011): Discourse Representation Theory

In this Handbook of Philosophical Logic chapter an information state records, for each world,
the witnesses of its discourse referents, so anaphoric potential lives below truth conditions and
the objects of context change are information states rather than propositions. Partee's marbles
(42), the argument for Definition 22, are rendered minimally as two states that determine the
same proposition (Definition 23(v)) but record different witnesses for their referent. In the
worked discourse (43), *John owns a donkey. It loves him.*, applying the context change potential
of the second sentence to the state the first expresses gives the state of their merge.

## Main statements

* `marble_worlds_eq_coin`, `marble_ne_coin`: the two marble states determine the same proposition
  and differ.
* `ccp_action`: updating the state of the first sentence of (43) with the second is the state of
  their merge, as the chapter remarks after Definition 24.

## References

* [kamp-vangenabith-reyle-2011]
-/

@[expose] public section

open FirstOrder FirstOrder.Language DRT
open DynamicSemantics

namespace KampVanGenabithReyle2011

/-! ### Partee's marbles: propositions are too coarse ((42), Definition 22)

The first sentences of (42)(i) and (ii), nine of the ten coins in the bag and one marble out
against nine of the ten marbles in the bag and one coin out, are truth-conditionally
equivalent but make different antecedents available for the following *it*. Two worlds
(`Bool`), one live referent (`Unit`), two entities (`Fin 2`): in world `true` a marble (`0`)
and a coin (`1`) are each missing, and the two states differ only in which one the referent
carries. -/

/-- In (42)(i) the referent carries the missing marble `0`, in world `true`. -/
def marbleState : State Bool Unit (Fin 2) :=
  {p | p.world = true ∧ p.assignment () = ((0 : Fin 2) : Flat (Fin 2))}

/-- In (42)(ii) the referent carries the missing coin `1`, in world `true`. -/
def coinState : State Bool Unit (Fin 2) :=
  {p | p.world = true ∧ p.assignment () = ((1 : Fin 2) : Flat (Fin 2))}

/-- The two states determine the same proposition, Definition 23(v). -/
theorem marble_worlds_eq_coin :
    Possibility.world '' marbleState = Possibility.world '' coinState := by
  ext w
  simp only [Set.mem_image]
  constructor
  · rintro ⟨p, ⟨hw, -⟩, rfl⟩
    exact ⟨⟨p.world, fun _ ↦ ((1 : Fin 2) : Flat (Fin 2))⟩, ⟨hw, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨hw, -⟩, rfl⟩
    exact ⟨⟨p.world, fun _ ↦ ((0 : Fin 2) : Flat (Fin 2))⟩, ⟨hw, rfl⟩, rfl⟩

/-- But the states differ, since the marble witness is not a coin witness. With
`marble_worlds_eq_coin`, this is Partee's argument that context change operates on information
states, not on propositions. -/
theorem marble_ne_coin : marbleState ≠ coinState := by
  intro h
  have hmem : (⟨true, fun _ ↦ ((0 : Fin 2) : Flat (Fin 2))⟩ : Possibility Bool Unit (Flat (Fin 2)))
      ∈ coinState := by
    rw [← h]
    exact ⟨rfl, rfl⟩
  exact absurd (Flat.coe_injective hmem.2) (by decide : (0 : Fin 2) ≠ 1)

/-! ### The action of a context change potential ((43), Definition 24) -/

/-- The relation symbols of the worked discourse (43). -/
inductive DRel : ℕ → Type
  | john : DRel 1
  | donkey : DRel 1
  | own : DRel 2
  | love : DRel 2

/-- The first-order language of the discourse (no function symbols). -/
def dLang : Language := ⟨fun _ ↦ Empty, DRel⟩

/-- The context DRS of (43), "John owns a donkey.", is `[x y | John x, donkey y, x owns y]`. -/
def context : DRS dLang ℕ :=
  .mk {0, 1} [.atom ⟨.john, ![0]⟩, .atom ⟨.donkey, ![1]⟩, .atom ⟨.own, ![0, 1]⟩]

/-- The update DRS of (43), "It loves him.", is `[z u | u loves z, z = x, u = y]`, the
pronouns resolved by equations to the context's referents. -/
def update : DRS dLang ℕ := .mk {2, 3} [.atom ⟨.love, ![3, 2]⟩, .eq 2 0, .eq 3 1]

theorem context_proper : context.IsProper := by decide

theorem update_improper : ¬ update.IsProper := by decide

/-- Its free referents are supplied by the context's universe, the condition under which the
context change potential of Definition 24 is defined on the context's state. -/
theorem update_bound : update.freeVarFinset ⊆ context.referents := by
  simp [update, context]; decide

theorem update_fresh : Disjoint update.referents (Condition.varFinsetL context.conditions) := by
  decide

/-- Applying the context change potential of the second sentence to the information state
expressed by the first yields the information state expressed by their merge, the DRS of the
whole discourse (43), as the chapter remarks after Definition 24. -/
theorem ccp_action {W M : Type*} [dLang.Structure M] :
    (update.transition (M := M) W context.referents update_bound).applyState
        (context.state W context_proper) =
      (context.merge update).state W (DRS.isProper_merge context_proper update_bound) :=
  DRS.state_merge W context update context_proper update_bound update_fresh

end KampVanGenabithReyle2011
