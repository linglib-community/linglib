module

public import Linglib.Semantics.Dynamic.DRS.Indexed
public import Mathlib.Data.Fin.VecNotation

/-!
# Kamp, van Genabith and Reyle (2011): Discourse Representation Theory

In this Handbook of Philosophical Logic chapter an information state records, for each world,
the witnesses of its discourse referents, so anaphoric potential lives below truth conditions and
the objects of context change are information states rather than propositions. Partee's marbles
(42), the argument for Definition 22, are rendered minimally as two DRSs true in the same worlds
of an intensional model whose information states record different witnesses for their referent.
In the worked discourse (43), *John owns a donkey. It loves him.*, applying the context change
potential of the second sentence to the state the first expresses gives the state of their merge.

## Main statements

* `marble_worlds_eq_coin`, `marble_ne_coin`: the states of the two marble DRSs determine the same
  proposition and differ.
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
(`Bool`), two entities (`Fin 2`), a marble `0` and a coin `1`, both out of the bag in world
`true` and both in it in world `false`. The first sentence of (i) contributes a referent for a
marble that is out, that of (ii) one for a coin that is out; the counting content of the
sentences is not rendered. -/

/-- The relation symbols of the marbles example. -/
inductive MRel : ℕ → Type
  | marble : MRel 1
  | coin : MRel 1
  | out : MRel 1

/-- The language of the marbles example (no function symbols). -/
def mLang : Language := ⟨fun _ ↦ Empty, MRel⟩

/-- The intensional model (Definition 18): `0` is a marble and `1` a coin in every world, and
both are out of the bag in world `true` only. -/
@[instance_reducible]
def bag : Bool → mLang.Structure (Fin 2) := fun w ↦
  { funMap := fun f _ ↦ f.elim
    RelMap := fun {n} R ↦ match n, R with
      | 1, .marble => fun a ↦ a 0 = 0
      | 1, .coin => fun a ↦ a 0 = 1
      | 1, .out => fun _ ↦ w = true }

/-- The first sentence of (42)(i), `[x | marble x, out x]`. -/
def marbleOut : DRS mLang ℕ := .mk {0} [.atom ⟨.marble, ![0]⟩, .atom ⟨.out, ![0]⟩]

/-- The first sentence of (42)(ii), `[x | coin x, out x]`. -/
def coinOut : DRS mLang ℕ := .mk {0} [.atom ⟨.coin, ![0]⟩, .atom ⟨.out, ![0]⟩]

theorem marbleOut_proper : marbleOut.IsProper := by decide

theorem coinOut_proper : coinOut.IsProper := by decide

private theorem exists_marbleOut_iff (w : Bool) :
    (∃ f g : ℕ → Fin 2, letI := bag w; DRS.toRelAt ∅ marbleOut f g) ↔ w = true :=
  ⟨fun ⟨_, _, _, _, hout, _⟩ ↦ hout, fun hw ↦
    ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ h ↦ absurd h (by simp), rfl, hw, trivial⟩⟩

private theorem exists_coinOut_iff (w : Bool) :
    (∃ f g : ℕ → Fin 2, letI := bag w; DRS.toRelAt ∅ coinOut f g) ↔ w = true :=
  ⟨fun ⟨_, _, _, _, hout, _⟩ ↦ hout, fun hw ↦
    ⟨fun _ ↦ 1, fun _ ↦ 1, fun _ h ↦ absurd h (by simp), rfl, hw, trivial⟩⟩

/-- The two states determine the same proposition, Definition 23(v). -/
theorem marble_worlds_eq_coin :
    Possibility.world '' marbleOut.state bag marbleOut_proper =
      Possibility.world '' coinOut.state bag coinOut_proper := by
  rw [DRS.image_world_state, DRS.image_world_state]
  ext w
  exact (exists_marbleOut_iff w).trans (exists_coinOut_iff w).symm

/-- The point of world `true` whose referent `0` carries the entity `d`. -/
def witness (d : Fin 2) : Possibility Bool ℕ (Flat (Fin 2)) :=
  ⟨true, fun v ↦ if v = 0 then ↑d else ⊥⟩

theorem witness_mem_marbleOut : witness 0 ∈ marbleOut.state bag marbleOut_proper := by
  refine (DRS.mem_state bag).mpr ⟨?_, fun _ ↦ 0, fun _ ↦ 0,
    ⟨fun _ h ↦ absurd h (by simp), rfl, rfl, trivial⟩, fun v hv ↦ ?_⟩
  · ext v
    by_cases hv : v = 0 <;> simp [witness, marbleOut, hv]
  · simp [witness, show v = 0 by simpa [marbleOut] using hv]

theorem witness_notMem_coinOut : witness 0 ∉ coinOut.state bag coinOut_proper := by
  intro h
  obtain ⟨-, f, g, ⟨-, hcoin, -⟩, hval⟩ := (DRS.mem_state bag).mp h
  have hg : g 0 = 1 := hcoin
  have h0 : ((0 : Fin 2) : Flat (Fin 2)) = ↑(g 0) := hval 0 (by simp [coinOut])
  rw [hg] at h0
  exact absurd (Flat.coe_injective h0) (by decide)

/-- But the states differ, since the marble witness is not a coin witness. With
`marble_worlds_eq_coin`, this is Partee's argument that context change operates on information
states, not on propositions. -/
theorem marble_ne_coin :
    marbleOut.state bag marbleOut_proper ≠ coinOut.state bag coinOut_proper :=
  fun h ↦ witness_notMem_coinOut (h ▸ witness_mem_marbleOut)

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

/-- The update's free referents are in the context's universe, so the context change potential of
Definition 24 is defined. -/
theorem update_bound : update.freeVarFinset ⊆ context.referents := by
  simp [update, context]; decide

theorem update_fresh :
    Disjoint update.referents (Condition.varFinsetL context.conditions \ context.referents) := by
  decide

/-- Applying the second sentence's context change potential to the first's information state yields
that of their merge (43) (Definition 24). -/
theorem ccp_action {W M : Type*} (interp : W → dLang.Structure M) :
    (update.transition interp context.referents update_bound).applyState
        (context.state interp context_proper) =
      (context.merge update).state interp (DRS.isProper_merge context_proper update_bound) :=
  DRS.state_merge interp context update context_proper update_bound update_fresh

end KampVanGenabithReyle2011
