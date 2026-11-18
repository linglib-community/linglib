module

public import Linglib.Semantics.Composition.Effect
public import Linglib.Semantics.Composition.Basic
public import Linglib.Semantics.ArgumentStructure.EventIdentification

/-!
# The basic rules of composition

The three rules by which sisters combine without effects, each a language over the types:
Functional Application in either order, Predicate Modification of two predicates of one type, and
Kratzer's Event Identification of a relation of individuals to events with a predicate of
events. Each has its structure on the domains of the types and the list of the rules that apply
to two types, and [no two of application and predicate modification apply to the same
daughters](##Interpreter.length_binaryRules_application_sum_predicateModification_le_one).

## Main definitions

* `Interpreter.Application`, `Interpreter.application`: functional application.
* `Interpreter.PredicateModification`, `Interpreter.predicateModification`: predicate
  modification.
* `Interpreter.EventIdentification`, `Interpreter.eventIdentification`: event identification,
  whose meaning is `ArgumentStructure.eventIdentification`.

## References

* [heim-kratzer-1998]
* [kratzer-1996]
* [bumford-charlow-2026]
-/

@[expose] public section

open ManySorted

namespace Interpreter

variable {B : Type}

/-- Functional application, forward and backward. -/
inductive Application : Ty B → Ty B → Ty B → Type
  /-- Forward application. -/
  | fa {a b : Ty B} : Application (a ⇒ b) a b
  /-- Backward application. -/
  | ba {a b : Ty B} : Application a (a ⇒ b) b

instance (f g : Eff B) (l r u : Ty B) : IsEmpty (Application (.comp f l) (.comp g r) u) :=
  ⟨nofun⟩

/-- Predicate modification, the conjunction of two predicates of one type. -/
inductive PredicateModification : Ty B → Ty B → Ty B → Type
  /-- Predicate modification. -/
  | pm {a : Ty B} : PredicateModification (a ⇒ .t) (a ⇒ .t) (a ⇒ .t)

instance (f : Eff B) (l r u : Ty B) : IsEmpty (PredicateModification (.comp f l) r u) :=
  ⟨nofun⟩

instance {L L' : Language (Ty B)} {σ : Signature (Ty B)} {u : Ty B} [IsEmpty (L.Functions σ u)]
    [IsEmpty (L'.Functions σ u)] : IsEmpty (Language.Sum L L' σ u) :=
  ⟨fun | .inl f => isEmptyElim f | .inr f => isEmptyElim f⟩

/-- The meaning of application. -/
@[simp] def Application.eval (D : B → Type) :
    {l r u : Ty B} → Application l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .fa, f, x => f x
  | _, _, _, .ba, x, f => f x

/-- The meaning of predicate modification. -/
@[simp] def PredicateModification.eval (D : B → Type) :
    {l r u : Ty B} → PredicateModification l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .pm, p, q => fun x ↦ p x ∧ q x

/-- Whichever daughter is a function of the other's type applies to it. -/
def Application.rules [DecidableEq B] (l r : Ty B) : List (Σ u, Application l r u) :=
  (match l with
    | .fn a b => if h : a = r then [⟨b, h ▸ .fa⟩] else []
    | _ => []) ++
  match r with
    | .fn a b => if h : a = l then [⟨b, h ▸ .ba⟩] else []
    | _ => []

theorem Application.mem_rules [DecidableEq B] {l r u : Ty B} (m : Application l r u) :
    ⟨u, m⟩ ∈ Application.rules l r := by
  cases m <;> simp [Application.rules]

/-- Two predicates of one type are conjoined. -/
def PredicateModification.rules [DecidableEq B] (l r : Ty B) :
    List (Σ u, PredicateModification l r u) :=
  match l with
  | .fn a .t => if h : r = (a ⇒ .t) then [⟨a ⇒ .t, by subst h; exact .pm⟩] else []
  | _ => []

theorem PredicateModification.mem_rules [DecidableEq B] {l r u : Ty B}
    (m : PredicateModification l r u) : ⟨u, m⟩ ∈ PredicateModification.rules l r := by
  cases m; simp [PredicateModification.rules]

/-- Functional Application, as a language over the types. -/
@[reducible] def application : Language (Ty B) := .mk₂ (fun _ _ ↦ PEmpty) Application

/-- Predicate Modification, as a language over the types. -/
@[reducible] def predicateModification : Language (Ty B) :=
  .mk₂ (fun _ _ ↦ PEmpty) PredicateModification

instance (D : B → Type) : (application (B := B)).Structure (Ty.Dom D) :=
  .mk₂ nofun (Application.eval D)

instance (D : B → Type) : (predicateModification (B := B)).Structure (Ty.Dom D) :=
  .mk₂ nofun (PredicateModification.eval D)

instance [DecidableEq B] : (application (B := B)).LocallyFinite :=
  .mk₂ (fun _ ↦ []) Application.rules nofun Application.mem_rules

instance [DecidableEq B] : (predicateModification (B := B)).LocallyFinite :=
  .mk₂ (fun _ ↦ []) PredicateModification.rules nofun PredicateModification.mem_rules

@[simp] theorem symbols_application [DecidableEq B] (l r : Ty B) :
    Language.LocallyFinite.symbols (L := application) (.prod (.of l) (.of r)) =
      Application.rules l r := rfl

@[simp] theorem symbols_application_of [DecidableEq B] (a : Ty B) :
    Language.LocallyFinite.symbols (L := application) (.of a) = [] := rfl

@[simp] theorem symbols_predicateModification_of [DecidableEq B] (a : Ty B) :
    Language.LocallyFinite.symbols (L := predicateModification) (.of a) = [] := rfl

@[simp] theorem symbols_predicateModification [DecidableEq B] (l r : Ty B) :
    Language.LocallyFinite.symbols (L := predicateModification) (.prod (.of l) (.of r)) =
      PredicateModification.rules l r := rfl

theorem Ty.ne_fn_self (a b : Ty B) : a ≠ (a ⇒ b) := fun h ↦ by
  have := congrArg Ty.size h
  simp only [Ty.size] at this
  omega

theorem Ty.ne_fn_fn_self (a b c d : Ty B) (h : a = (c ⇒ d)) : c ≠ (a ⇒ b) := fun h' ↦ by
  have := congrArg Ty.size h
  have := congrArg Ty.size h'
  simp only [Ty.size] at *
  omega

/-- At most one rule of application and predicate modification applies to two types: a type is
not a function of itself, nor of a function of itself. -/
theorem length_binaryRules_application_sum_predicateModification_le_one [DecidableEq B]
    (l r : Ty B) :
    (Language.LocallyFinite.binaryRules (L := application.sum predicateModification)
      l r).length ≤ 1 := by
  simp only [Language.LocallyFinite.symbols_sum, symbols_application,
    symbols_predicateModification, Application.rules, PredicateModification.rules,
    List.length_append, List.length_map]
  rcases l with _ | _ | ⟨a, b⟩ | _ <;> rcases r with _ | _ | ⟨c, d⟩ | _ <;>
    (try rcases b with _ | _ | _ | _) <;> simp <;> split_ifs <;> (try simp) <;>
    first
    | exact Ty.ne_fn_fn_self _ _ _ _ (by assumption) (by assumption)
    | (obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›; exact Ty.ne_fn_self _ _ (by assumption))

/-! ### The rule for given daughters -/

section Selection

private theorem Ty.ne_fn_fn (a b c : Ty B) : a ≠ ((a ⇒ b) ⇒ c) := fun h ↦ by
  have := congrArg Ty.size h
  simp only [Ty.size] at this
  omega

private theorem Ty.fn_ne_self (a b : Ty B) : (a ⇒ b) ≠ a := (Ty.ne_fn_self a b).symm

variable [DecidableEq B]

/-- A function and its argument combine by forward application alone. -/
@[simp] theorem Application.rules_fa (a b : Ty B) :
    Application.rules (a ⇒ b) a = [⟨b, .fa⟩] := by
  cases a <;> simp [Application.rules, Ty.ne_fn_fn]

/-- An argument and its function combine by backward application alone. -/
@[simp] theorem Application.rules_ba (a b : Ty B) :
    Application.rules a (a ⇒ b) = [⟨b, .ba⟩] := by
  cases a <;> simp [Application.rules, Ty.ne_fn_fn]

/-- Two predicates of one type do not apply to one another. -/
@[simp] theorem Application.rules_self (a : Ty B) :
    Application.rules (a ⇒ .t) (a ⇒ .t) = [] := by
  simp [Application.rules, Ty.ne_fn_self]

/-- Two predicates of one type combine by predicate modification. -/
@[simp] theorem PredicateModification.rules_self (a : Ty B) :
    PredicateModification.rules (a ⇒ .t) (a ⇒ .t) = [⟨a ⇒ .t, .pm⟩] := by
  simp [PredicateModification.rules]

/-- A function and its argument are not two predicates of one type. -/
@[simp] theorem PredicateModification.rules_fn_left (a b : Ty B) :
    PredicateModification.rules (a ⇒ b) a = [] := by
  rcases b with _ | _ | _ | _ <;> simp [PredicateModification.rules, Ty.ne_fn_self]

@[simp] theorem PredicateModification.rules_fn_right (a b : Ty B) :
    PredicateModification.rules a (a ⇒ b) = [] := by
  rcases a with _ | _ | ⟨a', _ | _ | _ | _⟩ | _ <;>
    simp [PredicateModification.rules, Ty.fn_ne_self]

end Selection

/-- Event identification, for individuals of type `x` and events of type `s`: a relation of
individuals to events and a predicate of events are conjoined at the event. -/
inductive EventIdentification (x s : Ty B) : Ty B → Ty B → Ty B → Type
  /-- Event identification, the relation on the left. -/
  | left : EventIdentification x s (x ⇒ s ⇒ .t) (s ⇒ .t) (x ⇒ s ⇒ .t)
  /-- Event identification, the relation on the right. -/
  | right : EventIdentification x s (s ⇒ .t) (x ⇒ s ⇒ .t) (x ⇒ s ⇒ .t)

/-- The meaning of event identification. -/
def EventIdentification.eval (D : B → Type) {x s : Ty B} :
    {l r u : Ty B} → EventIdentification x s l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .left, f, g => ArgumentStructure.eventIdentification f g
  | _, _, _, .right, g, f => ArgumentStructure.eventIdentification f g

/-- A relation of individuals to events is identified with a predicate of events, in either
order. -/
def EventIdentification.rules [DecidableEq B] (x s l r : Ty B) :
    List (Σ u, EventIdentification x s l r u) :=
  (if h : l = (x ⇒ s ⇒ .t) ∧ r = (s ⇒ .t) then
    [⟨x ⇒ s ⇒ .t, by obtain ⟨rfl, rfl⟩ := h; exact .left⟩]
  else []) ++
  if h : l = (s ⇒ .t) ∧ r = (x ⇒ s ⇒ .t) then
    [⟨x ⇒ s ⇒ .t, by obtain ⟨rfl, rfl⟩ := h; exact .right⟩]
  else []

theorem EventIdentification.mem_rules [DecidableEq B] {x s l r u : Ty B}
    (m : EventIdentification x s l r u) : ⟨u, m⟩ ∈ EventIdentification.rules x s l r := by
  cases m <;> simp [EventIdentification.rules]

/-- Event Identification, as a language over the types. -/
@[reducible] def eventIdentification (x s : Ty B) : Language (Ty B) :=
  .mk₂ (fun _ _ ↦ PEmpty) (EventIdentification x s)

instance (x s : Ty B) (D : B → Type) : (eventIdentification x s).Structure (Ty.Dom D) :=
  .mk₂ nofun (EventIdentification.eval D)

instance [DecidableEq B] (x s : Ty B) : (eventIdentification x s).LocallyFinite :=
  .mk₂ (fun _ ↦ []) (EventIdentification.rules x s) nofun EventIdentification.mem_rules

@[simp] theorem symbols_eventIdentification [DecidableEq B] (x s l r : Ty B) :
    Language.LocallyFinite.symbols (L := eventIdentification x s) (.prod (.of l) (.of r)) =
      EventIdentification.rules x s l r := rfl

end Interpreter
