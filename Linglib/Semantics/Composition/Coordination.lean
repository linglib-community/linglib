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

* `Coordinator.reading`: a coordinator's denotation at a conjoinable type.
* `Coordinator.readings`: its denotations at every conjoinable type.

## References

* [heim-kratzer-1998]
* [partee-rooth-1983]
-/

@[expose] public section

namespace Interpreter

variable {B : Type}

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
