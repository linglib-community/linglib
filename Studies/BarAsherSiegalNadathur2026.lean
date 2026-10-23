module

public import Studies.BarAsherSiegal2026

/-!
# Bar-Asher Siegal and Nadathur (2026): Modeling progress

This file formalizes the analysis of telic progressives in [bar-asher-siegal-nadathur-2026]. The
paper gives up the assumption that an accomplishment predicate `P` denotes only culminated
eventualities. Instead `P` introduces a causal model in which its culmination condition `C_P` is
a dependent variable, and the model's sufficient sets for `C_P` are the culmination procedures,
the recipes for `C_P`. A progressive is then about partial realization, not about modal
projections of culmination. `PROG(P)` is felicitous when `P` has a culmination procedure (33a).
It is true when the reference situation has initiated one, not completed any, and not completed a
sufficient set for non-culmination (34)–(36).

Situations assign each propositional variable 1, 0 or `u`, and a structural equation is read in
Kleene's three-valued way, as in Figure 1b and Table 2. Causal consistency (29) asks every settled
dependent variable to carry the value its equation gives. In a consistent situation, one fact is
causally necessary for another (30a) when the first is a causal ancestor of the second and every
consistent situation over the same variables that changes the first also changes the second. A
consistent situation is causally sufficient for one of its facts (30b) when each of its other
facts is necessary for it (`IsSufficient`). Its kernel is then a sufficient set, which contains
the effect itself.

On the dual-route door of Section 4.2 (`BarAsherSiegal2026.model`) the file checks:

* the two culmination procedures (38) and the three sufficient sets for non-culmination (39);
* that the electronic procedure must include the button, since without it the circuit is
  undetermined and the situation inconsistent (footnote 39);
* that *Nur is opening the door* (40) is true after the power has just been switched on, with
  handle and button unsettled (`prog_opening`);
* that (40) comes out false in the realistic context where the unturned handle and unpressed
  button complete a sufficient set for non-culmination, as the paper itself observes
  (`not_prog_realistic`);
* that the lock's state is a globally necessary condition (42), so that by (45) the progressive
  is undefined while the lock's state is unknown (43a) (`not_defined_of_lock_unknown`).

## Implementation notes

Situations are partial assignments over `Bool`. The three-valued value of an equation is the value
on which every completion of its parents' values agrees in every context (`Determines`), which is
Table 2's value for the door's equations. The situations over the same variables as `s` are its
reassignments (`reassign`), so necessity quantifies over `V → Bool`. The paper times the initiating
fact against the interval just before reference time; here a single pre-reference situation `s₀`
stands in for that interval. The paper prints the sufficient sets (39b) and (39c) without the effect
fact ⟨O,0⟩, which Definition (30b) puts in every sufficient set; `sNotElec` and `sNotCirc` include
it.

## TODO

The paper's repair for the realistic context of (40), which lets a sufficient set for
non-culmination be undone by updating a fungible background variable (Section 4.2), is left
open, as it is in the paper.

## References

* [bar-asher-siegal-nadathur-2026]
* [bar-asher-siegal-2026]
* [baglini-bar-asher-siegal-2025]
-/

@[expose] public section

namespace BarAsherSiegalNadathur2026

open CausalModel

/-! ### Situations and causal consistency -/

/-- A situation (28b): each variable is 1, 0, or undetermined. -/
abbrev Situation (V : Type*) := V → Flat Bool

section Model

variable {U V : Type*} (M : CausalModel U V fun _ ↦ Bool)

/-- The equation for `v` gives `b` under `s` when, in every context, every completion of the
values `s` assigns to `v`'s parents yields `b`. A completion assigns the parents alone, the other
variables being fixed at `false`, which the equation does not read. -/
def Determines (s : Situation V) (v : V) (b : Bool) : Prop :=
  ∀ y : V → Bool, (∀ w, ¬ M.graph.Adj w v → y w = false) →
    (∀ w, M.graph.Adj w v → ∀ c : Bool, s w = ↑c → y w = c) → ∀ u, M.eqn v u y = b

/-- Causal consistency (29): every settled dependent variable carries the value its equation
gives. -/
def Consistent (s : Situation V) : Prop :=
  ∀ v, (∃ w, M.graph.Adj w v) → ∀ b : Bool, s v = ↑b → Determines M s v b

/-- The situation over the same variables as `s` that assigns them the values of `b`. -/
def reassign [DecidableEq V] (s : Situation V) (b : V → Bool) : Situation V :=
  fun v ↦ if s v = ⊥ then ⊥ else ↑(b v)

/-- Causal necessity (30a): the fact `s` settles at `x` is necessary for the one it settles at
`y` when `x` is a causal ancestor of `y` and every consistent situation over the same variables
that changes `x` changes `y`. -/
def Necessary [DecidableEq V] (s : Situation V) (x y : V) : Prop :=
  Relation.TransGen M.graph.Adj x y ∧
    ∀ b : V → Bool, Consistent M (reassign s b) → reassign s b x ≠ s x → reassign s b y ≠ s y

/-- Causal sufficiency (30b): `s` is consistent, settles `y` at `b`, and each of its other facts
is necessary for that one. The kernel of `s` is then a sufficient set for ⟨y, b⟩. -/
def IsSufficient [DecidableEq V] (s : Situation V) (y : V) (b : Bool) : Prop :=
  Consistent M s ∧ s y = ↑b ∧ ∀ x, x ≠ y → s x ≠ ⊥ → Necessary M s x y

variable [DecidableEq V]

/-! ### The progressive -/

/-- Felicity (33a): the predicate has a culmination procedure, a sufficient set for its
culmination condition `c`. -/
def Felicitous (c : V) : Prop := ∃ S, IsSufficient M S c true

/-- INIT (36a): some fact of a culmination procedure holds at reference time `s` and did not hold
just before, in `s₀`. -/
def Init (c : V) (s₀ s : Situation V) : Prop :=
  ∃ S, IsSufficient M S c true ∧ ∃ v, ∃ b : Bool, S v = ↑b ∧ s v = ↑b ∧ s₀ v ≠ ↑b

/-- CUL (36b-i): some culmination procedure is completely realized. -/
def Cul (c : V) (s : Situation V) : Prop := ∃ S, IsSufficient M S c true ∧ S ≤ s

/-- TERM (36b-ii): some sufficient set for non-culmination is completely realized. -/
def Term (c : V) (s : Situation V) : Prop := ∃ S, IsSufficient M S c false ∧ S ≤ s

/-- The progressive (35): initiated and neither culminated nor terminated. -/
def Prog (c : V) (s₀ s : Situation V) : Prop := Init M c s₀ s ∧ ¬ (Cul M c s ∨ Term M c s)

/-- A globally necessary condition (42): the fact ⟨v, b⟩ is globally necessary for `c` when its
negation together with non-culmination is a sufficient set for non-culmination. -/
def GloballyNecessary (c v : V) (b : Bool) : Prop :=
  IsSufficient M [c ← false, v ← !b] c false

/-- Definedness (45): the progressive is defined when every globally necessary condition is
settled at reference time. -/
def Defined (c : V) (s : Situation V) : Prop :=
  ∀ v b, GloballyNecessary M c v b → s v ≠ ⊥

section Decidable

variable [Fintype V] [Fintype U] [DecidableRel M.graph.Adj]

instance (s : Situation V) (v : V) (b : Bool) : Decidable (Determines M s v b) := by
  unfold Determines; infer_instance

instance (s : Situation V) : Decidable (Consistent M s) := by
  unfold Consistent; infer_instance

instance (s : Situation V) (x y : V) : Decidable (Necessary M s x y) := by
  unfold Necessary; infer_instance

instance (s : Situation V) (y : V) (b : Bool) : Decidable (IsSufficient M s y b) := by
  unfold IsSufficient; infer_instance

instance (c v : V) (b : Bool) : Decidable (GloballyNecessary M c v b) := by
  unfold GloballyNecessary; infer_instance

end Decidable

variable {M}

theorem IsSufficient.eq_of_le {S s : Situation V} {y : V} {b : Bool}
    (h : IsSufficient M S y b) (hle : S ≤ s) : s y = ↑b :=
  Flat.coe_le_iff.1 (h.2.1 ▸ hle y)

theorem not_cul_or_term {c : V} {s : Situation V} (h : s c = ⊥) :
    ¬ (Cul M c s ∨ Term M c s) := by
  rintro (⟨S, hS, hle⟩ | ⟨S, hS, hle⟩) <;> exact Flat.coe_ne_bot ((hS.eq_of_le hle).symm.trans h)

end Model

/-! ### The dual-route door (Section 4.2) -/

open BarAsherSiegal2026 (V model)
open BarAsherSiegal2026.V

/-- The mechanical procedure (38a): handle turned, door unlocked, door open. -/
def sMech : Situation V := [handle ← true, lock ← false, doorOpens ← true]

/-- The electronic procedure (38b): door unlocked, power on, button pressed, circuit closed, door
open. -/
def sElec : Situation V :=
  [lock ← false, electricity ← true, button ← true, circuit ← true, doorOpens ← true]

/-- Non-culmination by the lock (39a). -/
def sLock : Situation V := [lock ← true, doorOpens ← false]

/-- Non-culmination with the handle unturned and no power (39b), with the effect fact. -/
def sNotElec : Situation V := [handle ← false, electricity ← false, doorOpens ← false]

/-- Non-culmination with the handle unturned and the button unpressed (39c), with the effect
fact. -/
def sNotCirc : Situation V :=
  [handle ← false, button ← false, circuit ← false, doorOpens ← false]

theorem sMech_sufficient : IsSufficient model sMech doorOpens true := by decide +kernel

theorem sElec_sufficient : IsSufficient model sElec doorOpens true := by decide +kernel

theorem sLock_sufficient : IsSufficient model sLock doorOpens false := by decide +kernel

theorem sNotElec_sufficient : IsSufficient model sNotElec doorOpens false := by decide +kernel

theorem sNotCirc_sufficient : IsSufficient model sNotCirc doorOpens false := by decide +kernel

/-- (39b) as printed, without the effect fact, is not a sufficient set under Definition (30b),
which puts the effect in every sufficient set. -/
theorem not_sufficient_as_printed :
    ¬ IsSufficient model [handle ← false, electricity ← false] doorOpens false := by
  decide

/-- *open the door* has a culmination procedure, so its progressive is felicitous (33a). -/
theorem felicitous : Felicitous model doorOpens := ⟨sMech, sMech_sufficient⟩

/-- The electronic procedure needs the button (footnote 39): without it the circuit, whose
equation reads the button, is settled against an undetermined equation value. -/
theorem not_sufficient_without_button :
    ¬ IsSufficient model
      [lock ← false, electricity ← true, circuit ← true, doorOpens ← true]
      doorOpens true := by
  decide

/-- Just before reference time the door is unlocked and the power is off. -/
def beforeSwitch : Situation V := [lock ← false, electricity ← false]

/-- At reference time Nur has switched the power on; handle and button are unsettled, as in the
first highlighted row of Table 2. -/
def switchedOn : Situation V := [lock ← false, electricity ← true]

/-- *Nur is opening the door* (40) is true once the power is switched on. -/
theorem prog_opening : Prog model doorOpens beforeSwitch switchedOn :=
  ⟨⟨sElec, sElec_sufficient, electricity, true, by decide, by decide, by decide⟩,
    not_cul_or_term (by decide)⟩

/-- The realistic context of (40), the second highlighted row of Table 2: Nur has turned neither
the handle nor the button, so the door is closed. -/
def realistic : Situation V :=
  [handle ← false, lock ← false, electricity ← true, button ← false, circuit ← false,
    doorOpens ← false]

/-- In the realistic context, a sufficient set for non-culmination (39c) makes (40) false, against
intuition. -/
theorem not_prog_realistic : ¬ Prog model doorOpens beforeSwitch realistic :=
  fun h ↦ h.2 (Or.inr ⟨sNotCirc, sNotCirc_sufficient, by decide⟩)

/-- The door's being unlocked is globally necessary for it to open (42): the lock alone makes a
sufficient set for non-culmination. -/
theorem lock_globallyNecessary : GloballyNecessary model doorOpens lock false := by
  decide +kernel

/-- (43a) *??Nur is opening the door*: while the lock's state is unknown, the progressive is not
defined, whatever Nur has done (45). -/
theorem not_defined_of_lock_unknown {s : Situation BarAsherSiegal2026.V} (h : s lock = ⊥) :
    ¬ Defined model doorOpens s :=
  fun hd ↦ hd lock false lock_globallyNecessary h

end BarAsherSiegalNadathur2026
