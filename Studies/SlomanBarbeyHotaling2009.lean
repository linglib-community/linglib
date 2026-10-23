module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Causation.CausalModel.Development
public import Linglib.Core.Relation.ReflTransGen

/-!
# Sloman, Barbey and Hotaling (2009): A Causal Model Theory of Cause, Enable, and Prevent

This file formalizes the causal model theory of [sloman-barbey-hotaling-2009]: the verbs refer
to the causal model of a discourse, and in the deterministic binary case their meanings are the
structural equations (2) to (4). *A causes B* asserts a link from A to B, `B := A`; *A enables B*
asserts a link, an accessory variable also linked to B, and A necessary for B, `B := A ∧ X`; and
*A prevents B* asserts a link along which A reduces B, `B := ¬A` with no accessory and `B := ¬A ∧ X`
or `B := ¬(A ∧ X)` with one. The verbs are
predicates on a causal model (`Causes`, `Enables`, `Prevents`), and the equations are models
(`causes`, `enables`, `prevents`, `preventsAnd`, `preventsNand`) that satisfy them
(`causes_Causes`, `enables_Enables`, `prevents_Prevents`, `preventsAnd_Prevents`,
`preventsNand_Prevents`). The paper's experiments follow from the equations: an effect follows
from its cause without any accessory, but from its enabler only once the accessory is settled
(Experiments 1 to 3, `causes_entails`, `enables_not_entails`, `enables_entails_of_accessory`),
and a one-link model is labelled *cause* while a two-link model is labelled *enable*
(Experiment 4, `not_enables_of_parents_eq_singleton`, `causes_not_Enables`). Two-premise
arguments are composed by substituting causes for effects, and the compositions the paper
works out come out as the equations it names: *causes* then *causes* is `C := A`
(`causesCauses_causes`), *allows* then *prevents*, or *allows* then *not B causes C*, is
`C := ¬(A ∧ X)`, the accessory form of *prevents* (`allowsPrevents_prevents`), *prevents* then
*prevents* is `C := A` (`preventsPrevents_causes`), and the three-premise argument of section
4.2 composes to `D := A` (`threePremise_causes`).

## Implementation notes

* A structural equation is a deterministic Boolean equation at the effect over its parents; the
  cause and the accessory variable are exogenous, read off the context. Entailment is strict
  causal entailment from an observation (`CausalModel.CausallyEntails`), on which an effect with
  an unsettled parent entails nothing: this is the paper's uncertainty when the accessory is
  unknown. Necessity is read in every context and under every intervention that leaves the
  effect open and turns the cause off: the effect is then off.
* The paper's experimental results stay in prose. In Experiments 1 to 3 confidence that the
  effect occurs was high only for a cause without an accessory and near the midpoint of the
  scale otherwise; in Experiment 4 one-link vignettes drew *cause* and two-link vignettes drew
  *enable*, *help* or *allow*. Of the sixteen two-premise argument forms of Goldvarg and
  Johnson-Laird's fourth experiment, the theory agrees with mental model theory on thirteen and
  predicts *A prevents C* for *allows* then *prevents* and for *allows* then *not B causes C*,
  and *A causes C* for *prevents* then *prevents*.

## References

* [sloman-barbey-hotaling-2009]
* [pearl-2000]
-/

@[expose] public section

namespace SlomanBarbeyHotaling2009

open CausalModel

section General

variable {U V : Type*} [DecidableEq V] (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]

/-- *A causes B* asserts a link from A to B. -/
def Causes (a b : V) : Prop := M.graph.Adj a b

instance [DecidableRel M.graph.Adj] (a b : V) : Decidable (Causes M a b) :=
  inferInstanceAs (Decidable (M.graph.Adj a b))

/-- A is necessary for B when, in every context and under every intervention that leaves B open
and turns A off, B is off. -/
def Necessary (a b : V) : Prop :=
  ∀ u (I : V → Flat Bool), I b = ⊥ → I a = ↑false → M.solve I u b = false

/-- *A enables B* asserts a link from A to B, an accessory variable also linked to B, and A
necessary for B. -/
def Enables (a b : V) : Prop :=
  M.graph.Adj a b ∧ (∃ x, x ≠ a ∧ M.graph.Adj x b) ∧ Necessary M a b

/-- *A prevents B* on the observation `s` asserts a link from A to B along which A being on
entails B off. -/
def Prevents (s : V → Flat Bool) (a b : V) : Prop :=
  M.graph.Adj a b ∧ M.CausallyEntails (Function.update s a ↑true) b false

instance [Fintype U] [Inhabited U] [Fintype V] [DecidableRel M.graph.Adj] (s : V → Flat Bool)
    (a b : V) : Decidable (Prevents M s a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The model realizes `c := a` on the observation `s`. -/
def EqCauses (s : V → Flat Bool) (a c : V) : Prop :=
  ∀ v : Bool, M.CausallyEntails (Function.update s a ↑v) c v

/-- The model realizes `c := ¬a` on the observation `s`. -/
def EqPrevents (s : V → Flat Bool) (a c : V) : Prop :=
  ∀ v : Bool, M.CausallyEntails (Function.update s a ↑v) c (!v)

variable {M}

omit [DecidableEq V] in
theorem not_enables_of_forall_adj {a b : V} (h : ∀ x, M.graph.Adj x b → x = a) :
    ¬ Enables M a b := by
  rintro ⟨-, ⟨x, hx, hxb⟩, -⟩
  exact hx (h x hxb)

theorem EqCauses.not_eqPrevents [Fintype U] [Inhabited U] [Fintype V]
    [DecidableRel M.graph.Adj] {s : V → Flat Bool} {a c : V} (h : EqCauses M s a c) :
    ¬ EqPrevents M s a c :=
  fun h' ↦ Bool.noConfusion ((h true).unique (h' true))

end General

/-! ### The equations of section 3 -/

/-- The cause, the accessory variable and the effect. -/
inductive V
  | A | X | B
  deriving DecidableEq, Fintype

/-- The context settles the cause A and the accessory X. -/
structure Context where
  A : Bool
  X : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- B reads its only parent A. -/
def oneLinkEdges : Finset (V × V) := {(.A, .B)}

/-- B reads A and the accessory X. -/
def twoLinkEdges : Finset (V × V) := {(.A, .B), (.X, .B)}

/-- A one-link model with the given equation at B, B's only parent being A. -/
def oneLinkModel (f : Bool → Bool) : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ oneLinkEdges⟩
  eqn | .A => fun u _ ↦ u.A | .X => fun u _ ↦ u.X | .B => fun _ x ↦ f (x .A)

/-- A two-link model with the given equation at B over A and the accessory X. -/
def twoLinkModel (f : Bool → Bool → Bool) : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ twoLinkEdges⟩
  eqn | .A => fun u _ ↦ u.A | .X => fun u _ ↦ u.X | .B => fun _ x ↦ f (x .A) (x .X)

instance (f : Bool → Bool) : DecidableRel (oneLinkModel f).graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ oneLinkEdges))

instance (f : Bool → Bool → Bool) : DecidableRel (twoLinkModel f).graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ twoLinkEdges))

instance (f : Bool → Bool) : (oneLinkModel f).IsAcyclic :=
  Finite.wellFounded_of_irrefl_transGen (r := fun w v ↦ (w, v) ∈ oneLinkEdges) (by decide)

instance (f : Bool → Bool → Bool) : (twoLinkModel f).IsAcyclic :=
  Finite.wellFounded_of_irrefl_transGen (r := fun w v ↦ (w, v) ∈ twoLinkEdges) (by decide)

/-- (2) *A causes B*: `B := A`. -/
abbrev causes : CausalModel Context V fun _ ↦ Bool := oneLinkModel id

/-- (3) *A enables B*: `B := A ∧ X`. -/
abbrev enables : CausalModel Context V fun _ ↦ Bool := twoLinkModel (· && ·)

/-- (4a) *A prevents B* with no accessory: `B := ¬A`. -/
abbrev prevents : CausalModel Context V fun _ ↦ Bool := oneLinkModel (!·)

/-- (4b) *A prevents B* with an accessory: `B := ¬A ∧ X`. -/
abbrev preventsAnd : CausalModel Context V fun _ ↦ Bool := twoLinkModel (fun a x ↦ !a && x)

/-- (4c) *A prevents B* with an accessory: `B := ¬(A ∧ X)`. -/
abbrev preventsNand : CausalModel Context V fun _ ↦ Bool :=
  twoLinkModel (fun a x ↦ !(a && x))

/-- The accessory present. -/
def accessory : V → Flat Bool := [.X ← true]

/-- *A causes B* holds of (2), and the model realizes `B := A`. -/
theorem causes_Causes : Causes causes .A .B ∧ EqCauses causes ⊥ .A .B :=
  ⟨by decide, fun v ↦ by cases v <;> decide⟩

theorem causes_entails : causes.CausallyEntails [.A ← true] .B true :=
  causes_Causes.2 true

theorem causes_not_Enables : ¬ Enables causes .A .B :=
  not_enables_of_forall_adj (by decide)

/-- *A enables B* holds of (3), which has the link, the accessory, and the necessity of A, B
being the conjunction of A and X. -/
theorem enables_Enables : Enables enables .A .B := by
  refine ⟨by decide, ⟨.X, by decide, by decide⟩, fun u I hb ha ↦ ?_⟩
  rw [solve_of_eq_bot hb]
  show (enables.solve I u .A && enables.solve I u .X) = false
  rw [solve_of_eq_coe ha, Bool.false_and]

theorem enables_not_entails :
    ¬ enables.CausallyEntails [.A ← true] .B true := by
  decide

theorem enables_entails_of_accessory :
    enables.CausallyEntails (Function.update accessory .A ↑true) .B true := by
  decide

/-- (4a) prevents: turning A on entails B off. -/
theorem prevents_Prevents : Prevents prevents ⊥ .A .B ∧ EqPrevents prevents ⊥ .A .B :=
  ⟨by decide, fun v ↦ by cases v <;> decide⟩

/-- (4b) and (4c) prevent when the accessory is present, and (4b) does so as the equation
`B := ¬A` on that observation. -/
theorem preventsAnd_Prevents :
    Prevents preventsAnd accessory .A .B ∧ EqPrevents preventsAnd accessory .A .B :=
  ⟨by decide, fun v ↦ by cases v <;> decide⟩

theorem preventsNand_Prevents :
    Prevents preventsNand accessory .A .B ∧ EqPrevents preventsNand accessory .A .B :=
  ⟨by decide, fun v ↦ by cases v <;> decide⟩

/-! ### Two-premise arguments, section 4.1

The premises *A relates to B* and *B relates to C* are structural equations, and the
conclusion is their composition, substituting the cause for the effect; the conclusion is the
equation the composed model realizes between A and C. -/

/-- The terms of a two-premise argument, with the first premise's accessory. -/
inductive W
  | A | X | B | C
  deriving DecidableEq, Fintype

/-- B reads A, and C reads B. -/
def composeOneEdges : Finset (W × W) := {(.A, .B), (.B, .C)}

/-- B reads A and the accessory X, and C reads B. -/
def composeTwoEdges : Finset (W × W) := {(.A, .B), (.X, .B), (.B, .C)}

/-- The composition of a first premise `B := f A` with a second premise `C := g B`. -/
def composeOne (f g : Bool → Bool) : CausalModel Context W fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ composeOneEdges⟩
  eqn
    | .A => fun u _ ↦ u.A
    | .X => fun u _ ↦ u.X
    | .B => fun _ x ↦ f (x .A)
    | .C => fun _ x ↦ g (x .B)

/-- The composition of a first premise `B := f A X` with a second premise `C := g B`. -/
def composeTwo (f : Bool → Bool → Bool) (g : Bool → Bool) :
    CausalModel Context W fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ composeTwoEdges⟩
  eqn
    | .A => fun u _ ↦ u.A
    | .X => fun u _ ↦ u.X
    | .B => fun _ x ↦ f (x .A) (x .X)
    | .C => fun _ x ↦ g (x .B)

instance (f g : Bool → Bool) : DecidableRel (composeOne f g).graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ composeOneEdges))

instance (f : Bool → Bool → Bool) (g : Bool → Bool) :
    DecidableRel (composeTwo f g).graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ composeTwoEdges))

instance (f g : Bool → Bool) : (composeOne f g).IsAcyclic :=
  Finite.wellFounded_of_irrefl_transGen (r := fun w v ↦ (w, v) ∈ composeOneEdges) (by decide)

instance (f : Bool → Bool → Bool) (g : Bool → Bool) : (composeTwo f g).IsAcyclic :=
  Finite.wellFounded_of_irrefl_transGen (r := fun w v ↦ (w, v) ∈ composeTwoEdges) (by decide)

/-- The first premise's accessory present. -/
def chainAccessory : W → Flat Bool := [.X ← true]

/-- (5) and (6): *A causes B*, *B causes C* compose to `C := A`, the conclusion *A causes C*. -/
theorem causesCauses_causes : EqCauses (composeOne id id) ⊥ .A .C :=
  fun v ↦ by cases v <;> decide

/-- *A allows B*, *B prevents C*, or equally *not B causes C*, compose to `C := ¬(A ∧ X)`, the
accessory form (4c) of *prevents*: with the accessory present, A prevents C. -/
theorem allowsPrevents_prevents : EqPrevents (composeTwo (· && ·) (!·)) chainAccessory .A .C :=
  fun v ↦ by cases v <;> decide

theorem preventsPrevents_causes : EqCauses (composeOne (!·) (!·)) ⊥ .A .C :=
  fun v ↦ by cases v <;> decide

/-! ### A three-premise argument, section 4.2 -/

/-- The terms of the three-premise argument. -/
inductive T
  | A | B | C | D
  deriving DecidableEq, Fintype

/-- B reads A, C reads B, and D reads C. -/
def threePremiseEdges : Finset (T × T) := {(.A, .B), (.B, .C), (.C, .D)}

/-- The context of the three-premise argument settles A. -/
structure ThreePremiseContext where
  A : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- The premises *A causes B*, *B causes not C* and *C causes not D* are `B := A`, `C := ¬B` and
`D := ¬C`. -/
def threePremise : CausalModel ThreePremiseContext T fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ threePremiseEdges⟩
  eqn
    | .A => fun u _ ↦ u.A
    | .B => fun _ x ↦ x .A
    | .C => fun _ x ↦ !x .B
    | .D => fun _ x ↦ !x .C

instance : DecidableRel threePremise.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ threePremiseEdges))

instance : threePremise.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

theorem threePremise_causes : EqCauses threePremise ⊥ .A .D :=
  fun v ↦ by cases v <;> decide

end SlomanBarbeyHotaling2009
