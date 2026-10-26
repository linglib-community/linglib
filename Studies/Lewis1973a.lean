module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Causation.CausalModel.Basic
public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Semantics.Reference.Context.Index
public import Mathlib.Logic.Relation

/-!
# Lewis (1973a): Causation

This file formalizes Lewis's counterfactual analysis of causation on
deterministic Boolean structural equation models. An event depends causally on another when,
had the cause not occurred, the effect would not have occurred (`lewisButFor`,
`lewisDependence`), and causation is the ancestral of causal dependence, a chain of
stepwise dependences (`lewisCausation`, via `Relation.TransGen`). Four scenarios exercise the
analysis: a single cause, a chain, in which the distal cause is a cause through two steps
(`Chain.chain_causation`), the common-cause case of the barometer and the storm, where
neither effect depends on the other (`Epiphenomena.barometer_not_causes_storm`), and
symmetric overdetermination, where neither of two sufficient causes passes the but-for test
(`Overdetermination.overdetermination_no_dependence_a`), the limitation the paper concedes.

## Implementation notes

The actual world is a context of a causal model, and the counterfactual is an intervention
setting the cause to `false` in that context (`CausalModel.solve`), so the analysis is the but-for
test of the model rather than a similarity ordering over worlds; the two agree on these
deterministic scenarios. The paper's treatment of preemption is not represented.

## References

* [lewis-1973a]
-/

@[expose] public section

namespace Lewis1973a

open CausalModel Relation Kaplan

section Dependence

variable {U W : Type*} [DecidableEq W] (M : CausalModel U W fun _ ↦ Bool) [M.IsAcyclic] (u : U)

/-- The but-for counterfactual holds when, had the cause not occurred, the effect would not have
occurred, the counterfactual being an intervention setting the cause to `false` in the actual
context `u`. -/
def lewisButFor (cause effect : W) : Prop :=
  M.solve [cause ← false] u effect ≠ true

/-- The effect depends causally on the cause (p. 562) when both occur and the effect would not
have occurred without the cause. -/
def lewisDependence (cause effect : W) : Prop :=
  M.solve ⊥ u cause = true ∧ M.solve ⊥ u effect = true ∧ lewisButFor M u cause effect

noncomputable instance [Fintype W] (cause effect : W) :
    Decidable (lewisButFor M u cause effect) :=
  inferInstanceAs (Decidable (_ ≠ _))

noncomputable instance [Fintype W] (cause effect : W) :
    Decidable (lewisDependence M u cause effect) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Causation is the ancestral of causal dependence (p. 563). -/
def lewisCausation (cause effect : W) : Prop :=
  Relation.TransGen (lewisDependence M u) cause effect

variable {M u}

theorem dependence_implies_causation {cause effect : W} (h : lewisDependence M u cause effect) :
    lewisCausation M u cause effect :=
  Relation.TransGen.single h

theorem not_lewisDependence_of_not_reflTransGen {cause effect : W}
    (h : ¬ ReflTransGen M.graph.Adj cause effect) : ¬ lewisDependence M u cause effect :=
  fun ⟨_, he, hbf⟩ ↦ hbf (by rw [solve_update_of_not_reflTransGen h]; exact he)

end Dependence

namespace SimpleCause

inductive V | a | b
  deriving DecidableEq, Fintype, Repr

/-- `b` follows `a`. -/
def edges : Finset (V × V) := {(.a, .b)}

/-- The context settles whether `a` occurs. -/
structure Context where
  a : Bool

/-- `b` occurs when `a` does. -/
def sem : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn | .a => fun u _ ↦ u.a | .b => fun _ x ↦ x .a

instance : DecidableRel sem.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : sem.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

theorem simple_butfor : lewisButFor sem ⟨true⟩ .a .b := by decide

theorem simple_dependence : lewisDependence sem ⟨true⟩ .a .b := by decide

theorem simple_causation : lewisCausation sem ⟨true⟩ .a .b :=
  dependence_implies_causation simple_dependence

end SimpleCause

namespace Chain

inductive V | a | b | c
  deriving DecidableEq, Fintype, Repr

/-- `b` follows `a`, and `c` follows `b`. -/
def edges : Finset (V × V) := {(.a, .b), (.b, .c)}

/-- The context settles whether `a` occurs. -/
structure Context where
  a : Bool

/-- The chain passes `a` on to `b` and `b` on to `c`. -/
def sem : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn | .a => fun u _ ↦ u.a | .b => fun _ x ↦ x .a | .c => fun _ x ↦ x .b

instance : DecidableRel sem.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : sem.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

theorem chain_direct_butfor : lewisButFor sem ⟨true⟩ .a .c := by decide

theorem chain_step_AB : lewisDependence sem ⟨true⟩ .a .b := by decide

theorem chain_step_BC : lewisDependence sem ⟨true⟩ .b .c := by decide

theorem chain_causation : lewisCausation sem ⟨true⟩ .a .c :=
  Relation.TransGen.trans
    (Relation.TransGen.single chain_step_AB)
    (Relation.TransGen.single chain_step_BC)

end Chain

namespace Epiphenomena

/-! The barometer reading and the storm are both effects of atmospheric pressure
(pp. 561 and 564–565): the analysis makes the pressure the cause of each and neither effect a
cause of the other. -/

inductive V | pressure | barometer | storm
  deriving DecidableEq, Fintype, Repr

/-- The pressure bears on the barometer and on the storm. -/
def edges : Finset (V × V) := {(.pressure, .barometer), (.pressure, .storm)}

/-- The context settles the pressure. -/
structure Context where
  pressure : Bool

/-- The barometer and the storm both follow the pressure. -/
def sem : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn
    | .pressure => fun u _ ↦ u.pressure
    | .barometer => fun _ x ↦ x .pressure
    | .storm => fun _ x ↦ x .pressure

instance : DecidableRel sem.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : sem.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

theorem pressure_causes_barometer : lewisDependence sem ⟨true⟩ .pressure .barometer := by
  decide

theorem pressure_causes_storm : lewisDependence sem ⟨true⟩ .pressure .storm := by decide

theorem barometer_not_causes_storm (u : Context) : ¬ lewisDependence sem u .barometer .storm :=
  not_lewisDependence_of_not_reflTransGen (by decide)

theorem storm_not_causes_barometer (u : Context) : ¬ lewisDependence sem u .storm .barometer :=
  not_lewisDependence_of_not_reflTransGen (by decide)

end Epiphenomena

namespace Overdetermination

/-! Symmetric overdetermination (fn. 12): with two sufficient causes both
present, neither is necessary, so neither passes the but-for test. -/

inductive V | a | b | e
  deriving DecidableEq, Fintype, Repr

/-- Both causes bear on the effect. -/
def edges : Finset (V × V) := {(.a, .e), (.b, .e)}

/-- The context settles the two causes. -/
structure Context where
  a : Bool
  b : Bool

/-- The effect occurs when either cause does. -/
def sem : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn | .a => fun u _ ↦ u.a | .b => fun u _ ↦ u.b | .e => fun _ x ↦ x .a || x .b

instance : DecidableRel sem.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : sem.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

theorem overdetermination_no_butfor_a : ¬ lewisButFor sem ⟨true, true⟩ .a .e := by decide

theorem overdetermination_no_butfor_b : ¬ lewisButFor sem ⟨true, true⟩ .b .e := by decide

theorem overdetermination_no_dependence_a : ¬ lewisDependence sem ⟨true, true⟩ .a .e := by
  decide

theorem overdetermination_no_dependence_b : ¬ lewisDependence sem ⟨true, true⟩ .b .e := by
  decide

end Overdetermination

end Lewis1973a
