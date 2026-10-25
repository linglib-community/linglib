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

`DRS.transition` is total, as partial operations are in mathlib: on a base missing a free
referent, outside the domain that condition (i) (p. 160) and Definition 24(i) give, it
existentially closes that referent, and theorems take the referential presupposition where they
need it. Distributivity and extensionality follow from the form of Definition 24(ii) alone, for
any transition, and do not use the absence of `□` and `◇`.

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
    Possibility.world '' marbleOut.state bag =
      Possibility.world '' coinOut.state bag := by
  rw [DRS.image_world_state, DRS.image_world_state]
  ext w
  exact (exists_marbleOut_iff w).trans (exists_coinOut_iff w).symm

/-- The point of world `true` whose referent `0` carries the entity `d`. -/
def witness (d : Fin 2) : Possibility Bool ℕ (Flat (Fin 2)) :=
  ⟨true, fun v ↦ if v = 0 then ↑d else ⊥⟩

theorem witness_mem_marbleOut : witness 0 ∈ marbleOut.state bag := by
  refine (DRS.mem_state bag).mpr ⟨?_, fun _ ↦ 0, fun _ ↦ 0,
    ⟨fun _ h ↦ absurd h (by simp), rfl, rfl, trivial⟩, fun v hv ↦ ?_⟩
  · ext v
    by_cases hv : v = 0 <;> simp [witness, marbleOut, hv]
  · simp [witness, show v = 0 by simpa [marbleOut] using hv]

theorem witness_notMem_coinOut : witness 0 ∉ coinOut.state bag := by
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
    marbleOut.state bag ≠ coinOut.state bag :=
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
    (update.transition interp context.referents).applyState (context.state interp) =
      (context.merge update).state interp :=
  DRS.state_merge interp context update context_proper update_fresh

/-! ### Regular context change potentials (pp. 160–162) -/

section Regular

variable {L : Language} {V W M : Type*} [DecidableEq V] (interp : W → L.Structure M)
  (K : DRS L V) (X : Finset V)

/-- The base of the output is the base of the input grown by the universe (p. 161, (ii)). -/
theorem ccp_base (I : State W V M) :
    State.UniformAt ↑(X ∪ K.referents) ((K.transition interp X).applyState I) :=
  Transition.uniformAt_applyState _ I

/-- A context change potential is distributive (p. 161, (iii)). -/
theorem ccp_distributive (I : State W V M) :
    (K.transition interp X).applyState I =
      ⋃ p ∈ I, (K.transition interp X).applyState ({p} : Set (Possibility W V (Flat M))) :=
  Transition.applyState_eq_biUnion _ I

/-- A context change potential only adds information: its output carries at least as much
information as its input (Definitions 25 and 27(ii)). -/
theorem ccp_informative (I : State W V M) : (K.transition interp X).applyState I ≤ I :=
  (DRS.transition_isExtension interp K X).applyState_le I

/-- A context change potential is extensional: states that coincide at a world have outputs
that coincide there (p. 162). -/
theorem ccp_extensional {I I' : State W V M} {w : W}
    (h : ∀ p : Possibility W V (Flat M), p.world = w → (p ∈ I ↔ p ∈ I'))
    {q : Possibility W V (Flat M)} (hq : q.world = w) :
    q ∈ (K.transition interp X).applyState I ↔ q ∈ (K.transition interp X).applyState I' :=
  Transition.applyState_congr_world _ h hq

/-- The state at which the referents in `X` take their values under `g`, at every world. -/
def fixedAt (X : Finset V) (g : V → M) : State W V M :=
  {p | p.domain = ↑X ∧ ∀ v ∈ X, p.assignment v = ↑(g v)}

/-- The information state `K` expresses relative to an assignment `g` of a base including its
free referents (Definition 29(ii)). -/
def relState (g : V → M) : State W V M :=
  (K.transition interp X).applyState (fixedAt X g)

/-- At the empty base the state relative to an assignment is the state the DRS expresses: Definition
29(ii) generalises Definition 22 to improper DRSs (p. 161). -/
theorem relState_empty (g : V → M) : relState interp K ∅ g = K.state interp := by
  have h : fixedAt (W := W) ∅ g = ⊤ := by
    ext p
    simp only [fixedAt, Finset.coe_empty, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, and_true, Possibility.domain_eq_empty_iff]
    exact State.mem_top.symm
  rw [relState, h, DRS.state]

/-- (44): at an extension of a point of the input with assignment `g`, the output of the context
change potential agrees with the state relative to `g`. -/
theorem mem_ccp_iff_mem_relState {I : State W V M} (hI : State.UniformAt ↑X I) (g : V → M)
    {p q : Possibility W V (Flat M)} (hp : p ∈ I) (hpg : ∀ v ∈ X, p.assignment v = ↑(g v))
    (hpq : p ≤ q) :
    q ∈ (K.transition interp X).applyState I ↔ q ∈ relState interp K X g := by
  have hu := DRS.transition_isExtension interp K X
  rw [hu.mem_applyState_iff_of_le hI hp hpq, relState,
    hu.mem_applyState_iff_of_le (I := fixedAt X g) (fun _ h => h.1) ⟨hI p hp, hpg⟩ hpq]

end Regular

end KampVanGenabithReyle2011
