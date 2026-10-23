module

public import Mathlib.Tactic.DeriveFintype
public import Studies.Glass2025
public import Linglib.Semantics.Causation.CausalModel.Basic
public import Linglib.Core.Relation.ReflTransGen

/-!
# Roberts and Özyıldız (2025): A causal explanation for the contrafactive gap

This file formalizes the paper's explanation of the absence of contrafactive predicates, verbs
that would presuppose the falsity of their complement while asserting belief in it. The
Predicate Lexicalization Constraint requires the presupposition of a predicate to be causally
upstream of its at-issue content in the normative model of belief formation, a causal chain
running from one variable to another when altering the first can alter the second,
`Upstream`. In the belief-formation model a fact generates indicators
for itself, experience of an indicator is acquaintance with it, acquaintance forms belief, and
a fact generates no indicator for its negation, `beliefModel`; the truth of a proposition
therefore manipulates belief in it, `know_plc`, whereas its falsity does not, `contra_plc`,
which is the gap. Predicates carrying the contrafactive inference are eventive: the Dutch
deception verb *wijsmaken* and *hallucinate* satisfy the constraint through an intervening
node of deception or distortion, `wijsmaken_plc`, and cutting that node returns the deficient
configuration. The postsuppositional Mandarin yǐwéi lies outside the constraint, so the
attestation table of [glass-2025] follows, `attested_iff`.

## Implementation notes

Models are deterministic Boolean causal models whose exogenous variables are the fields of a
context. The paper's first link makes the fact sufficient but not necessary for its indicators;
in the normative model, without forged evidence, the indicator copies the fact. The normative
context makes the experience conditions true and every other exogenous variable false, and the
manipulation test intervenes on the presupposed fact alone. The paper's causal chain is a template
over the choice of proposition and attitude holder, and the model is that template.

## References

* [T. Roberts, D. Özyıldız, *A causal explanation for the contrafactive gap*
  (2025)][roberts-ozyildiz-2025]
* [L. Glass, *Attested versus unattested contrafactive belief verbs* (2025)][glass-2025]
* [J. Pearl, *Causality: models, reasoning, and inference* (2009)][pearl-2000]
-/

@[expose] public section

namespace RobertsOzyildiz2025

open Glass2025 CausalModel Relation

/-- In the context `u`, the variable `c` is causally upstream of `e` when setting `c` true and
setting it false give `e` different values. -/
def Upstream {U V : Type*} [DecidableEq V] (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]
    (u : U) (c e : V) : Prop :=
  M.solve [c ← true] u e ≠ M.solve [c ← false] u e

noncomputable instance {U V : Type*} [Fintype V] [DecidableEq V]
    (M : CausalModel U V fun _ ↦ Bool)
    [M.IsAcyclic] (u : U) (c e : V) : Decidable (Upstream M u c e) :=
  inferInstanceAs (Decidable (_ ≠ _))

theorem not_upstream_of_not_reflTransGen {U V : Type*} [DecidableEq V]
    {M : CausalModel U V fun _ ↦ Bool} [M.IsAcyclic] {c e : V}
    (h : ¬ ReflTransGen M.graph.Adj c e) (u : U) : ¬ Upstream M u c e := fun hu ↦
  hu (by rw [solve_update_of_not_reflTransGen h, solve_update_of_not_reflTransGen h])

/-! ### The belief-formation model -/

/-- The variables of belief formation for a proposition and for its negation: the fact, an
indicator for it, the agent's experience of the indicator, acquaintance with it, and the
resulting belief. -/
inductive V
  | p | indicP | expP | acqP | beliefP
  | notP | indicNotP | expNotP | acqNotP | beliefNotP
  deriving DecidableEq, Fintype, Repr

/-- A fact generates an indicator for itself, experience of the indicator gives acquaintance
with it, and acquaintance forms belief; the chains for a proposition and for its negation do
not cross. -/
def edges : Finset (V × V) :=
  {(.p, .indicP), (.indicP, .acqP), (.expP, .acqP), (.acqP, .beliefP),
    (.notP, .indicNotP), (.indicNotP, .acqNotP), (.expNotP, .acqNotP), (.acqNotP, .beliefNotP)}

/-- The context settles the facts and whether the agent experiences their indicators, each
false unless set. -/
structure Context where
  p : Bool := false
  expP : Bool := false
  notP : Bool := false
  expNotP : Bool := false

/-- The normative model of belief formation: an indicator exists when its fact holds,
acquaintance is the existence of the indicator together with experience of it, and belief
follows acquaintance. The context settles the facts and the experience conditions. -/
def beliefModel : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn
    | .p => fun u _ ↦ u.p
    | .indicP => fun _ x ↦ x .p
    | .expP => fun u _ ↦ u.expP
    | .acqP => fun _ x ↦ x .indicP && x .expP
    | .beliefP => fun _ x ↦ x .acqP
    | .notP => fun u _ ↦ u.notP
    | .indicNotP => fun _ x ↦ x .notP
    | .expNotP => fun u _ ↦ u.expNotP
    | .acqNotP => fun _ x ↦ x .indicNotP && x .expNotP
    | .beliefNotP => fun _ x ↦ x .acqNotP

instance : DecidableRel beliefModel.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : beliefModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- In the normative context the agent experiences whatever indicators exist. -/
def normative : Context := { expP := true, expNotP := true }

/-! ### The Predicate Lexicalization Constraint -/

theorem know_plc : Upstream beliefModel normative .p .beliefP := by decide

theorem contra_plc : ¬ Upstream beliefModel normative .notP .beliefP :=
  not_upstream_of_not_reflTransGen (by decide) _

theorem contra_plc' : ¬ Upstream beliefModel normative .p .beliefNotP :=
  not_upstream_of_not_reflTransGen (by decide) _

/-- The constraint's verdict on the profiles of [glass-2025]: for a factive and for the
hypothetical strong contrafactive, whether the presupposed fact manipulates belief in the
complement; a nonfactive presupposes nothing and yǐwéi's falsity inference is a
postsupposition on the output context, so the constraint does not apply. -/
def SatisfiesPLC : Profile → Prop
  | .factive => Upstream beliefModel normative .p .beliefP
  | .strongContrafactive => Upstream beliefModel normative .notP .beliefP
  | .nonfactive | .weakContrafactive => True

theorem attested_iff : ∀ pr : Profile, pr.Attested ↔ SatisfiesPLC pr
  | .factive => ⟨fun _ ↦ know_plc, fun _ ↦ trivial⟩
  | .strongContrafactive => ⟨False.elim, fun h ↦ contra_plc h⟩
  | .nonfactive | .weakContrafactive => Iff.rfl

/-! ### Eventive predicates with the contrafactive inference -/

/-- The variables of *wijsmaken*: the complement's falsity, the object's prior lack of the
belief, the subject's fooling the object, and the object's resulting belief. -/
inductive W
  | notRich | notBeliefPrior | fool | beliefRich
  deriving DecidableEq, Fintype, Repr

/-- Falsity and prior lack of belief are jointly necessary for fooling, which is sufficient
for the belief. -/
def wijsmakenEdges : Finset (W × W) :=
  {(.notRich, .fool), (.notBeliefPrior, .fool), (.fool, .beliefRich)}

/-- The context settles the complement's falsity and the object's prior lack of the belief. -/
structure WijsmakenContext where
  notRich : Bool := false
  notBeliefPrior : Bool := false

/-- The model of *wijsmaken*, and the model with the eventive node cut, on which the belief
no longer depends on anything. -/
def wijsmaken (eventive : Bool) : CausalModel WijsmakenContext W fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ wijsmakenEdges⟩
  eqn
    | .notRich => fun u _ ↦ u.notRich
    | .notBeliefPrior => fun u _ ↦ u.notBeliefPrior
    | .fool => fun _ x ↦ x .notRich && x .notBeliefPrior
    | .beliefRich => fun _ x ↦ eventive && x .fool

instance (eventive : Bool) : DecidableRel (wijsmaken eventive).graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ wijsmakenEdges))

instance (eventive : Bool) : (wijsmaken eventive).IsAcyclic :=
  Finite.wellFounded_of_irrefl_transGen (r := fun w v ↦ (w, v) ∈ wijsmakenEdges) (by decide)

/-- The context in which the object did not already hold the belief. -/
def noPriorBelief : WijsmakenContext := { notBeliefPrior := true }

theorem wijsmaken_plc : Upstream (wijsmaken true) noPriorBelief .notRich .beliefRich := by
  decide

theorem wijsmaken_cut : ¬ Upstream (wijsmaken false) noPriorBelief .notRich .beliefRich := by
  decide

/-- The variables of *hallucinate*: the complement's falsity, the distortion of the input,
and the resulting belief. -/
inductive H
  | notLoves | distortion | beliefLoves
  deriving DecidableEq, Fintype, Repr

/-- Falsity is necessary for distortion, which is necessary for the belief. -/
def hallucinateEdges : Finset (H × H) := {(.notLoves, .distortion), (.distortion, .beliefLoves)}

/-- The context settles the complement's falsity. -/
structure HallucinateContext where
  notLoves : Bool := false

/-- The model of *hallucinate*, and the model with the distortion cut. -/
def hallucinate (eventive : Bool) : CausalModel HallucinateContext H fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ hallucinateEdges⟩
  eqn
    | .notLoves => fun u _ ↦ u.notLoves
    | .distortion => fun _ x ↦ x .notLoves
    | .beliefLoves => fun _ x ↦ eventive && x .distortion

instance (eventive : Bool) : DecidableRel (hallucinate eventive).graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ hallucinateEdges))

instance (eventive : Bool) : (hallucinate eventive).IsAcyclic :=
  Finite.wellFounded_of_irrefl_transGen (r := fun w v ↦ (w, v) ∈ hallucinateEdges) (by decide)

theorem hallucinate_plc :
    Upstream (hallucinate true) {} .notLoves .beliefLoves := by
  decide

theorem hallucinate_cut :
    ¬ Upstream (hallucinate false) {} .notLoves .beliefLoves := by
  decide

end RobertsOzyildiz2025
