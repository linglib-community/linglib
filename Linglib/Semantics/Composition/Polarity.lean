/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.ProjectivitySignature
public import Linglib.Semantics.Composition.Interpret
public import Linglib.Semantics.Composition.Rules

/-!
# The class of a derivation as a function of a trace

Put a trace where a phrase stands, and the value of a derivation is a function of the value of
the trace: the environment of the phrase. This file computes a class of maps that contains that
function, a projectivity signature, from the derivation alone. Each word comes with the classes
it is in for its successive arguments, as *no* is antitone in its restrictor and in its scope.
The marking of a derivation says either that it is free of the trace, with the classes it is
still in for the arguments it takes, or that it depends on the trace, with the class it is in as
a function of it. At an application, a function free of the trace composes its class with the
class of its argument, and a function that depends on the trace keeps its class at an argument
free of it. [The marking is sound](##Interpreter.marking_sound): whatever it says of a derivation
holds of the value of the derivation.

## Main definitions

* `Interpreter.Marking`: free of the trace or dependent on it, with classes.
* `Interpreter.marking`: the marking of a derivation by functional application.
* `Interpreter.Signed`: a value is in the listed classes in its successive arguments.

## Implementation notes

* A class is stated between the algebras of two conjoinable types. Where a type has no algebra,
  such as the entities or the numbers, nothing is claimed of a map out of it or into it.
* The marking is an upper bound: the function is in the class, and it may be in a smaller one.
  That a position is not in a class, as a context that is downward entailing and not
  anti-additive is not, needs values at which the property fails.
* The derivations are those of functional application. A binder and the other rules of
  composition are not covered.

## References

* [icard-2012]
* [heim-kratzer-1998]
-/

@[expose] public section

open ManySorted ManySorted.Language NaturalLogic

namespace Interpreter

variable {B : Type} {W : Ty B → Type} {Γ : ℕ → Ty B} {D : B → Type}

/-- What is known of a constituent with respect to a trace: it is free of the trace, and is in the
listed classes in its successive arguments, or it depends on the trace, and is in a class as a
function of it. -/
inductive Marking
  | free (sigs : List ProjectivitySignature)
  | marked (φ : ProjectivitySignature)
  deriving DecidableEq

/-- The results of the terms of a shape. -/
def Markings : Signature (Ty B) → Type
  | .nil => PUnit
  | .of _ => Marking
  | .prod σ τ => Markings σ × Markings τ

/-- The result of a function applied to an argument of type `a`. A function free of the trace
passes on the class of its argument, composed with its own, when the argument's type has an
algebra. A function that depends on the trace keeps its class at an argument free of it. -/
def Marking.app (a : Ty B) : Marking → Marking → Marking
  | .free (_ :: σs), .free _ => .free σs
  | .free [], .free _ => .free []
  | .free (σ :: _), .marked φ => .marked (if a.Conjoinable then σ * φ else ⊤)
  | .free [], .marked _ => .marked ⊤
  | .marked φ, .free _ => .marked φ
  | .marked _, .marked _ => .marked ⊤

/-- The result of a rule of application from the results of its daughters. -/
def Marking.ofRule : (σ : Signature (Ty B)) → (u : Ty B) →
    (application (B := B)).Functions σ u → Markings σ → Marking
  | .prod (.of l) (.of r'), _, f, r =>
    match l, r', f with
    | _, a, .fa => Marking.app a r.1 r.2
    | a, _, .ba => Marking.app a r.2 r.1
  | .of _, _, f, _ => nomatch f
  | .nil, _, f, _ => nomatch f
  | .prod .nil _, _, f, _ => nomatch f
  | .prod (.prod _ _) _, _, f, _ => nomatch f
  | .prod (.of _) .nil, _, f, _ => nomatch f
  | .prod (.of _) (.prod _ _), _, f, _ => nomatch f

variable (sigs : ∀ {a : Ty B}, W a → List ProjectivitySignature) (n : ℕ)

/-- The result of a leaf: a word has the classes its entry gives, the trace `n` is the identity,
and nothing is known of another trace. -/
def Marking.ofLeaf : {a : Ty B} → Leaf W Γ a → Marking
  | _, .word x => .free (sigs x)
  | _, .trace m => if m = n then .marked 1 else .free []

/-- The result of a derivation with respect to the trace `n`. -/
def marking : {σ : Signature (Ty B)} → (application (B := B)).Term (Leaf W Γ) σ → Markings σ
  | _, .var x => Marking.ofLeaf sigs n x
  | _, .func f r => Marking.ofRule _ _ f (marking r)
  | _, .prod a b => (marking a, marking b)
  | _, .nil => PUnit.unit

/-! ### Soundness -/

variable (D)

/-- The class `φ` holds of a map between the algebras of two conjoinable types. -/
def HoldsAt {τ a : Ty B} (hτ : τ.Conjoinable) (ha : a.Conjoinable) (φ : ProjectivitySignature)
    (F : τ.Dom D → a.Dom D) : Prop :=
  letI := Ty.Dom.completeBooleanAlgebra D τ hτ
  letI := Ty.Dom.completeBooleanAlgebra D a ha
  φ.HoldsFor F

/-- A value is in the listed classes in its successive arguments, at every value of the earlier
ones, wherever the types have algebras. -/
def Signed : List ProjectivitySignature → (a : Ty B) → a.Dom D → Prop
  | [], _, _ => True
  | σ :: σs, .fn a b, f =>
    (∀ (ha : a.Conjoinable) (hb : b.Conjoinable), HoldsAt D ha hb σ f) ∧ ∀ x, Signed σs b (f x)
  | _ :: _, .t, _ | _ :: _, .base _, _ | _ :: _, .comp _ _, _ => True

variable {D} {τ : Ty B} (hτ : τ.Conjoinable)

/-- A result is sound for a function of the trace's value. -/
def Marking.Sound (a : Ty B) : Marking → (τ.Dom D → a.Dom D) → Prop
  | .free σs, F => (∀ x y, F x = F y) ∧ ∀ x, Signed D σs a (F x)
  | .marked φ, F => ∀ ha : a.Conjoinable, HoldsAt D hτ ha φ F

theorem holdsAt_top {a : Ty B} (ha : a.Conjoinable) (F : τ.Dom D → a.Dom D) :
    HoldsAt D hτ ha ⊤ F := by
  let := Ty.Dom.completeBooleanAlgebra D τ hτ
  let := Ty.Dom.completeBooleanAlgebra D a ha
  exact ProjectivitySignature.holdsFor_top F

theorem holdsAt_eval {a b : Ty B} (hb : b.Conjoinable) {φ : ProjectivitySignature}
    {F : τ.Dom D → (a ⇒ b).Dom D} (hF : HoldsAt D hτ (a := a ⇒ b) hb φ F) (v : a.Dom D) :
    HoldsAt D hτ hb φ fun x ↦ F x v := by
  let := Ty.Dom.completeBooleanAlgebra D τ hτ
  let := Ty.Dom.completeBooleanAlgebra D b hb
  have he : ProjectivitySignature.addMult.HoldsFor fun f : a.Dom D → b.Dom D ↦ f v :=
    ProjectivitySignature.holdsFor_addMult_iff.2 ⟨⟨fun _ _ ↦ rfl, rfl⟩, fun _ _ ↦ rfl, rfl⟩
  have := he.comp hF
  rwa [show ProjectivitySignature.addMult * φ = φ from one_mul φ] at this

theorem Marking.app_sound {a b : Ty B} {rf rx : Marking} {Ff : τ.Dom D → (a ⇒ b).Dom D}
    {Fx : τ.Dom D → a.Dom D} (hf : rf.Sound hτ (a ⇒ b) Ff) (hx : rx.Sound hτ a Fx) :
    (Marking.app a rf rx).Sound hτ b fun x ↦ Ff x (Fx x) := by
  have x₀ : τ.Dom D := (Ty.Dom.completeBooleanAlgebra D τ hτ).bot
  cases rf with
  | free σs =>
    cases rx with
    | free _ =>
      cases σs with
      | nil =>
        exact ⟨fun x y ↦ by show Ff x (Fx x) = Ff y (Fx y); rw [hf.1 x y, hx.1 x y],
          fun _ ↦ trivial⟩
      | cons σ σs =>
        exact ⟨fun x y ↦ by show Ff x (Fx x) = Ff y (Fx y); rw [hf.1 x y, hx.1 x y],
          fun x ↦ (hf.2 x).2 (Fx x)⟩
    | marked φ =>
      cases σs with
      | nil => exact fun hb ↦ holdsAt_top hτ hb _
      | cons σ σs =>
        refine fun (hb : b.Conjoinable) ↦ ?_
        by_cases ha : a.Conjoinable
        · have h1 : HoldsAt D ha hb σ (Ff x₀) := (hf.2 x₀).1 ha hb
          have h2 : HoldsAt D hτ ha φ Fx := hx ha
          have he : (fun x ↦ Ff x (Fx x)) = Ff x₀ ∘ Fx := funext fun x ↦ by rw [hf.1 x x₀]; rfl
          show HoldsAt D hτ hb (if a.Conjoinable then σ * φ else ⊤) _
          simp only [ha, ↓reduceIte, he]
          let := Ty.Dom.completeBooleanAlgebra D τ hτ
          let := Ty.Dom.completeBooleanAlgebra D a ha
          let := Ty.Dom.completeBooleanAlgebra D b hb
          exact ProjectivitySignature.HoldsFor.comp (f := Ff x₀) (g := Fx) h1 h2
        · show HoldsAt D hτ hb (if a.Conjoinable then σ * φ else ⊤) _
          simp only [ha, ↓reduceIte]
          exact holdsAt_top hτ hb _
  | marked φ =>
    cases rx with
    | free _ =>
      refine fun (hb : b.Conjoinable) ↦ ?_
      have he : (fun x ↦ Ff x (Fx x)) = fun x ↦ Ff x (Fx x₀) :=
        funext fun x ↦ by rw [hx.1 x x₀]
      show HoldsAt D hτ hb φ _
      rw [he]
      exact holdsAt_eval hτ hb (hf hb) (Fx x₀)
    | marked _ => exact fun hb ↦ holdsAt_top hτ hb _

/-- Results are sound for functions of the trace's value, at each shape. -/
def Sound : (σ : Signature (Ty B)) → Markings σ → (τ.Dom D → σ.Interpret (Ty.Dom D)) → Prop
  | .nil, _, _ => True
  | .of a, r, F => Marking.Sound hτ a r F
  | .prod σ₁ σ₂, r, F => Sound σ₁ r.1 (fun x ↦ (F x).1) ∧ Sound σ₂ r.2 (fun x ↦ (F x).2)

theorem ofRule_sound : ∀ (σ : Signature (Ty B)) (u : Ty B)
    (f : (application (B := B)).Functions σ u) (r : Markings σ)
    (F : τ.Dom D → σ.Interpret (Ty.Dom D)), Sound hτ σ r F →
      (Marking.ofRule σ u f r).Sound hτ u fun x ↦
        (inferInstance : (application (B := B)).Structure (Ty.Dom D)).funMap f (F x)
  | .prod (.of l) (.of r'), u, f, r, F, h => by
    change Application l r' u at f
    cases f
    · exact Marking.app_sound hτ h.1 h.2
    · exact Marking.app_sound hτ h.2 h.1
  | .of _, _, f, _, _, _ => nomatch f
  | .nil, _, f, _, _, _ => nomatch f
  | .prod .nil _, _, f, _, _, _ => nomatch f
  | .prod (.prod _ _) _, _, f, _, _, _ => nomatch f
  | .prod (.of _) .nil, _, f, _, _, _ => nomatch f
  | .prod (.of _) (.prod _ _), _, f, _, _, _ => nomatch f

section Main

variable {sigs : ∀ {a : Ty B}, W a → List ProjectivitySignature} {n : ℕ}
  {ρ : ∀ {a : Ty B}, W a → (∀ m, (Γ m).Dom D) → a.Dom D} (g : ∀ m, (Γ m).Dom D)

/-- The pass is sound: whatever it reports of a derivation holds of the derivation's value as a
function of the value of the trace, provided each word is in the classes its entry gives and
does not itself read the trace. -/
theorem marking_sound (hτ : (Γ n).Conjoinable)
    (hsig : ∀ {a : Ty B} (w : W a) (g : ∀ m, (Γ m).Dom D), Signed D (sigs w) a (ρ w g))
    (hfree : ∀ {a : Ty B} (w : W a) (x : (Γ n).Dom D), ρ w (Function.update g n x) = ρ w g) :
    ∀ {σ : Signature (Ty B)} (t : (application (B := B)).Term (Leaf W Γ) σ),
      Sound hτ σ (marking sigs n t) fun x ↦
        t.realize inferInstance fun {_} l ↦ Leaf.val ρ l (Function.update g n x) := by
  intro σ t
  induction t with
  | var l =>
    cases l with
    | word w =>
      exact ⟨fun x y ↦ by show ρ w _ = ρ w _; rw [hfree, hfree],
        fun x ↦ by show Signed D _ _ (ρ w _); rw [hfree]; exact hsig w g⟩
    | trace m =>
      by_cases h : m = n
      · subst h
        show Marking.Sound hτ _ (if m = m then .marked 1 else .free []) _
        simp only [↓reduceIte]
        intro ha
        have he : (fun x : (Γ m).Dom D ↦ Function.update g m x m) = id :=
          funext fun x ↦ Function.update_self ..
        show HoldsAt D hτ ha 1 fun x ↦ Function.update g m x m
        rw [he]
        let := Ty.Dom.completeBooleanAlgebra D (Γ m) hτ
        exact ProjectivitySignature.holdsFor_addMult_id
      · show Marking.Sound hτ _ (if m = n then .marked 1 else .free []) _
        simp only [h, ↓reduceIte]
        exact ⟨fun x y ↦ by
          show Function.update g n x m = Function.update g n y m
          rw [Function.update_of_ne h, Function.update_of_ne h], fun _ ↦ trivial⟩
  | func f r ih => exact ofRule_sound hτ _ _ f _ _ ih
  | prod a b iha ihb => exact ⟨iha, ihb⟩
  | nil => trivial

end Main

end Interpreter
