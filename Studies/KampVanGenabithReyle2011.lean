module

public import Linglib.Semantics.Dynamic.DRS.ContextChange
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
The context change potentials of DRSs are regular (Definition 27) and relate to the states DRSs
express relative to an assignment (Definition 29) as (44) states.

## Main statements

* `marble_worlds_eq_coin`, `marble_ne_coin`: the states of the two marble DRSs determine the same
  proposition and differ.
* `ccp_action`: updating the state of the first sentence of (43) with the second is the state of
  their merge, as the chapter remarks after Definition 24.
* `ccp_informative`: a context change potential only adds information (Definition 27(ii)).
* `mem_ccp_iff_mem_relState`: (44).

## Implementation notes

`DRS.ccp` is total on information states: on a state whose base misses a free referent, outside
the domain that condition (i) (p. 160) and Definition 24(i) give, an atomic condition on that
referent fails. Definition 22 is Definition 29 at the empty assignment by definition
(`DRS.state`), the generalisation to improper DRSs of p. 161. Distributivity and extensionality
follow from the form of Definition 24(ii) alone and do not use the absence of `□` and `◇`.

## Errata

Definition 27(i) defines a regular context change potential on the states whose base includes its
own base, where the informal condition (i) it summarises (p. 160) and Definition 24(i) use its
referential presupposition, for a DRS the free referents: for the update of (43), `{z, u}`
against `{x, y}`. `update_bound` is Definition 24(i)'s condition for (43).

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

set_option linter.style.haveILetI false in
private theorem marbleOut_isTrue_iff (w : Bool) :
    (letI := bag w; marbleOut.IsTrue (Fin 2)) ↔ w = true := by
  constructor
  · rintro ⟨g, -, -, -, ⟨v, -, hout⟩, -⟩
    exact hout
  · rintro rfl
    letI := bag true
    refine ⟨PartialAssign.single 0 0, ?_⟩
    rw [marbleOut, DRS.verifies_mk]
    simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true, Condition.holds_atom]
    exact ⟨bot_le, by simp,
      ⟨![0], fun i => by rw [Subsingleton.elim i 0]; simp, rfl⟩,
      ⟨![0], fun i => by rw [Subsingleton.elim i 0]; simp, rfl⟩⟩

set_option linter.style.haveILetI false in
private theorem coinOut_isTrue_iff (w : Bool) :
    (letI := bag w; coinOut.IsTrue (Fin 2)) ↔ w = true := by
  constructor
  · rintro ⟨g, -, -, -, ⟨v, -, hout⟩, -⟩
    exact hout
  · rintro rfl
    letI := bag true
    refine ⟨PartialAssign.single 0 1, ?_⟩
    rw [coinOut, DRS.verifies_mk]
    simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true, Condition.holds_atom]
    exact ⟨bot_le, by simp,
      ⟨![1], fun i => by rw [Subsingleton.elim i 0]; simp, rfl⟩,
      ⟨![1], fun i => by rw [Subsingleton.elim i 0]; simp, rfl⟩⟩

/-- The two states determine the same proposition, Definition 23(v). -/
theorem marble_worlds_eq_coin :
    Possibility.world '' marbleOut.state bag = Possibility.world '' coinOut.state bag := by
  rw [DRS.image_world_state, DRS.image_world_state]
  ext w
  exact (marbleOut_isTrue_iff w).trans (coinOut_isTrue_iff w).symm

/-- The point of world `true` whose referent `0` carries the entity `d`. -/
def witness (d : Fin 2) : Possibility Bool ℕ (Flat (Fin 2)) :=
  ⟨true, PartialAssign.single 0 d⟩

set_option linter.style.haveILetI false in
theorem witness_mem_marbleOut : witness 0 ∈ marbleOut.state bag := by
  letI := bag true
  show marbleOut.Verifies ⊥ (PartialAssign.single 0 0)
  rw [marbleOut, DRS.verifies_mk]
  simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true, Condition.holds_atom]
  exact ⟨bot_le, by simp,
    ⟨![0], fun i => by rw [Subsingleton.elim i 0]; simp, rfl⟩,
    ⟨![0], fun i => by rw [Subsingleton.elim i 0]; simp, rfl⟩⟩

theorem witness_notMem_coinOut : witness 0 ∉ coinOut.state bag := by
  rintro ⟨-, -, ⟨v, hv, hcoin⟩, -⟩
  have h0 : (witness 0).assignment 0 = ↑(v 0) := hv 0
  have h1 : (witness 0).assignment 0 = ↑(0 : Fin 2) := by simp [witness]
  have h2 : (0 : Fin 2) = v 0 := Flat.coe_injective (h1.symm.trans h0)
  have h3 : v 0 = 1 := hcoin
  rw [← h2] at h3
  exact absurd h3 (by decide)

/-- But the states differ, since the marble witness is not a coin witness. With
`marble_worlds_eq_coin`, this is Partee's argument that context change operates on information
states, not on propositions. -/
theorem marble_ne_coin : marbleOut.state bag ≠ coinOut.state bag :=
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

-- Definition 24
theorem update_bound : update.freeVarFinset ⊆ context.referents := by
  simp [update, context]; decide

theorem update_fresh :
    Disjoint update.referents (Condition.varFinsetL context.conditions \ context.referents) := by
  decide

/-- Applying the second sentence's context change potential to the first's information state
yields that of their merge (43) (Definition 24). -/
theorem ccp_action {W M : Type*} (interp : W → dLang.Structure M) :
    update.ccp interp (context.state interp) = (context.merge update).state interp :=
  DRS.state_merge interp context update update_fresh

/-! ### Regular context change potentials (pp. 160–162) -/

section Regular

variable {L : Language} {V W M : Type*} (interp : W → L.Structure M) (K : DRS L V)

-- p. 161, (ii)
theorem ccp_base {X : Set V} {I : State W V M} (hI : State.UniformAt X I) :
    State.UniformAt (X ∪ ↑K.referents) (K.ccp interp I) := by
  intro q hq
  obtain ⟨p, hp, -, hv⟩ := (DRS.mem_ccp interp).mp hq
  have h := DRS.VerifiesAt.domain_eq interp hv
  rwa [Possibility.domain_assignment, Possibility.domain_assignment, hI p hp] at h

-- p. 161, (iii)
theorem ccp_distributive : CCP.IsDistributive (K.ccp interp) :=
  Update.image_isDistributive _

/-- A context change potential only adds information: its output carries at least as much
information as its input (Definitions 25 and 27(ii)). -/
theorem ccp_informative (I : State W V M) : K.ccp interp I ≤ I :=
  DRS.ccp_le interp I

-- p. 162
theorem ccp_extensional {I I' : State W V M} {w : W}
    (h : ∀ p : Possibility W V (Flat M), p.world = w → (p ∈ I ↔ p ∈ I'))
    {q : Possibility W V (Flat M)} (hq : q.world = w) :
    q ∈ K.ccp interp I ↔ q ∈ K.ccp interp I' := by
  rw [DRS.mem_ccp, DRS.mem_ccp]
  exact exists_congr fun p => and_congr_left fun hrest => h p (hrest.1.trans hq)

/-- (44): at an extension of a point of the input, the context change potential agrees with the
state the DRS expresses relative to that point's assignment (Definition 29). -/
theorem mem_ccp_iff_mem_relState {X : Set V} {I : State W V M} (hI : State.UniformAt X I)
    {p q : Possibility W V (Flat M)} (hp : p ∈ I) (hpq : p ≤ q) :
    q ∈ K.ccp interp I ↔ q ∈ K.relState interp p.assignment := by
  rw [DRS.mem_ccp, DRS.mem_relState]
  constructor
  · rintro ⟨p', hp', hw, hv⟩
    have he : p' = p := by
      rw [(Possibility.le_iff_eq_restrict (hI p' hp')).mp
          ⟨hw, Pi.le_def.mp (DRS.VerifiesAt.le interp hv)⟩,
        ← (Possibility.le_iff_eq_restrict (hI p hp)).mp hpq]
    rw [← he, ← hw]
    exact hv
  · intro hv
    refine ⟨p, hp, hpq.1, ?_⟩
    rw [hpq.1]
    exact hv

end Regular

end KampVanGenabithReyle2011
