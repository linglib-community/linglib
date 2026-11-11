module

public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Coordinator

/-!
# Coordinators at the conjoinable types

A type is conjoinable when it ends in `t`, and its domain is then a complete Boolean algebra,
pointwise. A coordinator has a denotation at each such type, $\lambda q\,\lambda p.\ c\{p, q\}$,
which Functional Application composes with its coordinands, and predicate modification [is the
conjunctive one at a type of predicates](##Coordinator.predicateModification_eval_eq_reading).

## Main definitions

* `Interpreter.Ty.Conjoinable`: the types that end in `t`.
* `Coordinator.reading`: a coordinator's denotation at a conjoinable type.
* `Coordinator.readings`: its denotations at every conjoinable type.

## References

* [heim-kratzer-1998]
* [partee-rooth-1983]
-/

@[expose] public section

namespace Interpreter

variable {B : Type}

/-- A type is conjoinable when it ends in `t` ([partee-rooth-1983]). -/
def Ty.Conjoinable : Ty B → Prop
  | .t => True
  | .fn _ b => b.Conjoinable
  | .comp (.R _) b => b.Conjoinable
  | .base _ | .comp .S _ | .comp (.W _) _ | .comp (.C _) _ | .comp .M _
  | .comp .F _ => False

instance Ty.decidableConjoinable : DecidablePred (Ty.Conjoinable (B := B))
  | .t => .isTrue trivial
  | .fn _ b => Ty.decidableConjoinable b
  | .comp (.R _) b => Ty.decidableConjoinable b
  | .base _ | .comp .S _ | .comp (.W _) _ | .comp (.C _) _ | .comp .M _
  | .comp .F _ => .isFalse id

/-- The domain of a conjoinable type carries the pointwise complete Boolean algebra
([partee-rooth-1983]). -/
@[instance_reducible]
def Ty.Dom.completeBooleanAlgebra (D : B → Type) :
    (ty : Ty B) → ty.Conjoinable → CompleteBooleanAlgebra (ty.Dom D)
  | .t, _ => inferInstanceAs (CompleteBooleanAlgebra Prop)
  | .fn _ b, h => letI := completeBooleanAlgebra D b h; inferInstance
  | .comp (.R _) b, h => letI := completeBooleanAlgebra D b h; inferInstance
  | .base _, h | .comp .S _, h | .comp (.W _) _, h | .comp (.C _) _, h | .comp .M _, h
  | .comp .F _, h => h.elim

end Interpreter

namespace Coordinator

open Interpreter

variable {B : Type} {D : B → Type}

/-- A coordinator at a conjoinable type $\tau$ denotes $\lambda q\,\lambda p.\ c\{p, q\}$, of type
$\langle\tau,\langle\tau,\tau\rangle\rangle$, taking its right coordinand first, as in
$[X\ [c\ Y]]$. -/
def reading (c : Coordinator) (τ : Ty B) (h : τ.Conjoinable) : Σ a : Ty B, a.Dom D :=
  ⟨τ ⇒ τ ⇒ τ, fun q p ↦ letI := Ty.Dom.completeBooleanAlgebra D τ h; c.denote {p, q}⟩

/-- A coordinator's readings are its denotations at every conjoinable type. -/
def readings (c : Coordinator) : Set (Σ a : Ty B, a.Dom D) :=
  Set.range fun τ : {τ : Ty B // τ.Conjoinable} ↦ c.reading τ τ.2

/-- A conjunctive coordinator's reading is the meet of its coordinands. -/
theorem reading_of_conjunctive {c : Coordinator} (hc : c.role = .conjunctive) {τ : Ty B}
    (h : τ.Conjoinable) : (c.reading τ h : Σ a : Ty B, a.Dom D) =
      ⟨τ ⇒ τ ⇒ τ, fun q p ↦ letI := Ty.Dom.completeBooleanAlgebra D τ h; p ⊓ q⟩ := by
  unfold reading
  congr 2
  funext q p
  let := Ty.Dom.completeBooleanAlgebra D τ h
  exact (denote_of_conjunctive hc _).trans sInf_pair

/-- A disjunctive coordinator's reading is the join of its coordinands. -/
theorem reading_of_disjunctive {c : Coordinator} (hc : c.role = .disjunctive) {τ : Ty B}
    (h : τ.Conjoinable) : (c.reading τ h : Σ a : Ty B, a.Dom D) =
      ⟨τ ⇒ τ ⇒ τ, fun q p ↦ letI := Ty.Dom.completeBooleanAlgebra D τ h; p ⊔ q⟩ := by
  unfold reading
  congr 2
  funext q p
  let := Ty.Dom.completeBooleanAlgebra D τ h
  exact (denote_of_disjunctive hc _).trans sSup_pair

/-- Predicate modification is the conjunctive reading at a type of predicates. -/
theorem predicateModification_eval_eq_reading {c : Coordinator} (hc : c.role = .conjunctive)
    {a : Ty B} (x y : (a ⇒ .t).Dom D) :
    PredicateModification.eval D .pm x y = (c.reading (D := D) (a ⇒ .t) trivial).2 y x := by
  let := Ty.Dom.completeBooleanAlgebra D (a ⇒ .t) trivial
  exact ((denote_of_conjunctive hc {x, y}).trans sInf_pair).symm

end Coordinator
