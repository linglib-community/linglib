module

public import Linglib.Syntax.Voice.Basic
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Composition.Ty
public import Linglib.Fragments.English.Verbs.Inventory
public import Mathlib.Tactic.FinCases

/-!
# Chierchia (1984): Topics in the syntax and semantics of infinitives and gerunds

This file formalizes the control theory of [chierchia-1984]. Infinitival and gerundive
complements denote properties, not propositions, and control is not movement of PRO but
entailment: the Control Principle is a meaning postulate on a verb taking a property
complement, that it holds of the property and its arguments exactly when a designated argument
has the property throughout the situations the verb's conversational background selects
([kratzer-1981]), so the controller is fixed by the predicate's meaning rather than by syntactic
configuration. Visser's and Bach's generalizations follow: a subject-control verb cannot
passivize and an object-control verb cannot detransitivize, since either alternation removes
the argument the postulate needs. The control classes of chapter IV are cut by whether the
postulate applies and whether the controller must be expressed. The theorems derive the
controller's having the property from the postulate, and, in the Fragment, which alternations
it blocks from what the voice does to the controlling participant of the verb's diathesis: the
passive exactly when the controller is the subject, the antipassive exactly when it is the
object.

## Implementation notes

* The conversational background is the two-parameter one of [kratzer-1991], a modal base and an
  ordering source, and the entailment is necessity over it; the possibility that *allow*
  needs is not instantiated.

## References

* [chierchia-1984]
* [kratzer-1981]
* [kratzer-1991]
-/

@[expose] public section

namespace Chierchia1984

open Modality

variable {E W Args : Type*}

/-! ### The Control Principle (chapter IV) -/

/-- A verb taking a property complement, with the Control Principle as its meaning postulate:
the verb holds of a property and its arguments at a world exactly when the argument it controls
has the property throughout the situations its conversational background selects, what is aimed
at for *try*, what is imposed for *force*. -/
structure ControlVerb (E W Args : Type*) where
  sem : (E → W → Prop) → Args → W → Prop
  controller : Args → E
  accessible : Args → W → Set W
  control : ∀ P args w, sem P args w ↔ ∀ w' ∈ accessible args w, P (controller args) w'

/-- A subject-control verb's one argument is its controller. -/
abbrev SubjectControlVerb (E W : Type*) := ControlVerb E W E

/-- An object-control verb controls the first of its object and subject. -/
abbrev ObjectControlVerb (E W : Type*) := ControlVerb E W (E × E)

/-- The control verb of a modal base and an ordering source, [kratzer-1991]'s form of the
background, whose controller has the property throughout the best accessible worlds. -/
def ControlVerb.ofKratzer (base ordering : Background W)
    (controller : Args → E) : ControlVerb E W Args where
  sem P args w := necessity base ordering (P (controller args)) w
  controller := controller
  accessible _ w := bestWorlds base ordering w
  control _ _ _ := necessity_iff _ _ _ _

variable (v : ControlVerb E W Args)

/-- The controller has the property in every situation the background selects. -/
theorem ControlVerb.controller_has {P : E → W → Prop} {args : Args} {w : W}
    (h : v.sem P args w) : ∀ w' ∈ v.accessible args w, P (v.controller args) w' :=
  (v.control P args w).1 h

/-- Over a reflexive background the controller has the property at the world itself. -/
theorem ControlVerb.controller_has_self (hrefl : ∀ args w, w ∈ v.accessible args w)
    {P : E → W → Prop} {args : Args} {w : W} (h : v.sem P args w) : P (v.controller args) w :=
  v.controller_has h w (hrefl args w)

/-! ### Visser's and Bach's generalizations (chapter IV) -/

/-- Visser's generalization says that a faithful passive of a subject-control verb, one whose
truth witnesses a truth of the active, can only guarantee that some entity has the property in
the selected situations, since the argument the postulate would name is gone. -/
theorem visser (v : SubjectControlVerb E W) (pass : (E → W → Prop) → W → Prop)
    (faithful : ∀ P w, pass P w → ∃ x, v.sem P x w) {P : E → W → Prop} {w : W}
    (h : pass P w) : ∃ x, ∀ w' ∈ v.accessible x w, P (v.controller x) w' :=
  let ⟨x, hx⟩ := faithful P w h
  ⟨x, v.controller_has hx⟩

/-- Bach's generalization says the same of a faithful detransitive of an object-control verb. -/
theorem bach (v : ObjectControlVerb E W) (detrans : (E → W → Prop) → E → W → Prop)
    (faithful : ∀ P y w, detrans P y w → ∃ args, v.sem P args w) {P : E → W → Prop} {y : E}
    {w : W} (h : detrans P y w) : ∃ args, ∀ w' ∈ v.accessible args w, P (v.controller args) w' :=
  let ⟨args, hv⟩ := faithful P y w h
  ⟨args, v.controller_has hv⟩

/-! ### Control classes (chapter IV, section 1) -/

/-- The three control classes are obligatory control, where the Control Principle fixes a
controller that must be expressed, *try* and *persuade* alike; semi-obligatory control, where
the controller may stay implicit, *decide*, *recommend*; and prominence control, where discourse
rather than the postulate fixes it, *bother*, *be dangerous*. -/
inductive ControlClass where
  | obligatory
  | semiObligatory
  | prominence
  deriving DecidableEq, Repr

/-- The Control Principle governs the first two classes. -/
def ControlClass.HasControlPrinciple : ControlClass → Prop
  | .obligatory => True
  | .semiObligatory => True
  | .prominence => False

instance : DecidablePred ControlClass.HasControlPrinciple
  | .obligatory => inferInstanceAs (Decidable True)
  | .semiObligatory => inferInstanceAs (Decidable True)
  | .prominence => inferInstanceAs (Decidable False)

/-- The class of a Fragment verb, obligatory control for every verb with a controller, the
Fragment recording neither an implicit controller nor the prominence verbs. -/
def ControlClass.ofVerb (v : Verb) : Option ControlClass :=
  if v.HasController then some .obligatory else none

/-! ### Which alternations the postulate blocks -/

open Voice

variable {n : ℕ}

/-- The Control Principle blocks a voice on a diathesis's frame that removes the controlling
participant from core-term status, since the argument the postulate needs is then gone. -/
def Blocks (d : Diathesis n) (va : Voice) : Prop :=
  ∃ c ∈ d.controller, ∃ s ∈ d.links.get c, (va.fate s).RemovesFromCoreStatus

instance (d : Diathesis n) (va : Voice) : Decidable (Blocks d va) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A diathesis passivizes when the postulate does not block the passive of its frame. -/
def Passivizable (d : Diathesis n) : Prop := ¬ Blocks d (passive d.toArgumentFrame)

instance (d : Diathesis n) : Decidable (Passivizable d) :=
  inferInstanceAs (Decidable (¬ Blocks d _))

/-! ### The Fragment's control verbs -/

section Fragment

open English
open English.Verbs hiding Verb

/-- The control verbs of the Fragment, the attitude verbs *want*, *hope* and *promise* included. -/
def controlVerbs : List Verb :=
  [try_.toVerb, manage.toVerb, begin_.toVerb, stop.toVerb, continue_.toVerb, fail.toVerb,
    persuade.toVerb, force.toVerb, want.toVerb, hope.toVerb, promise.toVerb]

/-- Every control verb of the Fragment is a control verb in the dissertation's sense, with a
participant controlling its complement. -/
theorem fragment_control_verbs : ∀ v ∈ controlVerbs, v.HasController := by
  decide

/-- Visser's generalization holds in the Fragment. The passive of a diathesis's frame blocks
exactly when its controller is the subject, as for *try* and *promise Bill to come*, and not when
it is the object, as for *persuade* and *force*. -/
theorem blocks_passive_iff : ∀ v ∈ controlVerbs, ∀ d ∈ v.valency.diatheses,
    Blocks d (passive d.toArgumentFrame) ↔
      d.controllerRole = some .S ∨ d.controllerRole = some .A := by
  decide

/-- Bach's generalization holds in the Fragment. The antipassive blocks exactly when the
controller is the object, so *promise to come* stands beside *promise Bill to come*, and
*persuade to come* does not. -/
theorem blocks_antipassive_iff : ∀ v ∈ controlVerbs, ∀ d ∈ v.valency.diatheses,
    Blocks d antipassive ↔ d.controllerRole = some .P := by
  decide

/-- At the Fragment's control verbs with one diathesis, the passivizability the postulate
derives agrees with the stored flag. -/
theorem passivizable_iff :
    ∀ v ∈ [try_.toVerb, persuade.toVerb, force.toVerb], ∀ d ∈ v.valency.basic?,
      Passivizable d ↔ v.passivizable = true := by
  decide

/-- The semantic type of a clausal complement, a proposition for a finite clause and a property
for a nonfinite one, the type distinction of chapter I. -/
def complementTy (fr : ArgumentFrame) : Option Montague.Ty :=
  if fr.HasClausal then some (if fr.HasFinite then .t else .et) else none

/-- Control verbs take property-denoting complements; *believe*, no control verb, takes a finite
clause denoting a proposition. -/
theorem control_complements_property :
    (∀ v ∈ [try_.toVerb, want.toVerb], v.valency.frames.head?.bind complementTy = some .et) ∧
      believe.toVerb.valency.frames.head?.bind complementTy = some .t ∧
      ¬ believe.toVerb.HasController := by
  decide

end Fragment

end Chierchia1984
