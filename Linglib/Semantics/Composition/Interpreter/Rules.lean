module

public import Linglib.Semantics.Composition.Interpreter.Effect
public import Linglib.Semantics.Composition.Interpreter.Basic
public import Linglib.Semantics.Composition.EventIdentification

/-!
# The basic rules of composition

The grammars of the three rules by which sisters combine without effects: Functional Application
in either order, Predicate Modification of two predicates of one type, and Kratzer's Event
Identification of a relation of individuals to events with a predicate of events. Each has its
structure on the domains of the types and the list of the rules that apply to two types, and
[no two of application and predicate modification apply to the same
daughters](##Interpreter.Grammar.length_binaryRules_application_sum_predicateModification_le_one).

## Main definitions

* `Interpreter.Application`, `Interpreter.Grammar.application`: functional application.
* `Interpreter.PredicateModification`, `Interpreter.Grammar.predicateModification`: predicate
  modification.
* `Interpreter.EventIdentification`, `Interpreter.Grammar.eventIdentification`: event
  identification, whose meaning is `ArgumentStructure.eventIdentification`.

## References

* [heim-kratzer-1998]
* [kratzer-1996]
* [bumford-charlow-2026]
-/

@[expose] public section

namespace Interpreter

variable {B : Type}

/-- Functional application, forward and backward. -/
inductive Application : Ty B → Ty B → Ty B → Type
  /-- Forward application. -/
  | fa {a b : Ty B} : Application (a ⇒ b) a b
  /-- Backward application. -/
  | ba {a b : Ty B} : Application a (a ⇒ b) b

/-- Predicate modification, the conjunction of two predicates of one type. -/
inductive PredicateModification : Ty B → Ty B → Ty B → Type
  /-- Predicate modification. -/
  | pm {a : Ty B} : PredicateModification (a ⇒ .t) (a ⇒ .t) (a ⇒ .t)

/-- The meaning of application. -/
@[simp] def Application.eval (D : B → Type) :
    {l r u : Ty B} → Application l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .fa, f, x => f x
  | _, _, _, .ba, x, f => f x

/-- The meaning of predicate modification. -/
@[simp] def PredicateModification.eval (D : B → Type) :
    {l r u : Ty B} → PredicateModification l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .pm, p, q => fun x ↦ p x ∧ q x

/-- The grammar of functional application. -/
@[reducible] def Grammar.application : Grammar (Ty B) := ⟨fun _ _ ↦ Empty, Application⟩

instance (D : B → Type) : (Grammar.application (B := B)).language.Structure (Ty.Dom D) :=
  Grammar.structure nofun (Application.eval D)

/-- Whichever daughter is a function of the other's type applies to it. -/
instance [DecidableEq B] : (Grammar.application (B := B)).LocallyFinite where
  unaryRules _ := []
  binaryRules l r :=
    (match l with
      | .fn a b => if h : a = r then [⟨b, h ▸ .fa⟩] else []
      | _ => []) ++
    match r with
      | .fn a b => if h : a = l then [⟨b, h ▸ .ba⟩] else []
      | _ => []
  mem_unaryRules := nofun
  mem_binaryRules m := by cases m <;> simp

/-- The grammar of predicate modification. -/
@[reducible] def Grammar.predicateModification : Grammar (Ty B) :=
  ⟨fun _ _ ↦ Empty, PredicateModification⟩

instance (D : B → Type) :
    (Grammar.predicateModification (B := B)).language.Structure (Ty.Dom D) :=
  Grammar.structure nofun (PredicateModification.eval D)

/-- Two predicates of one type are conjoined. -/
instance [DecidableEq B] : (Grammar.predicateModification (B := B)).LocallyFinite where
  unaryRules _ := []
  binaryRules l r :=
    match l with
    | .fn a .t => if h : r = (a ⇒ .t) then [⟨a ⇒ .t, by subst h; exact .pm⟩] else []
    | _ => []
  mem_unaryRules := nofun
  mem_binaryRules m := by cases m; simp

@[simp] theorem Grammar.funMap_application_sum_predicateModification_inl {D : B → Type}
    {l r u : Ty B} (m : Application l r u) (p : l.Dom D × r.Dom D) :
    MSFirstOrder.Language.Structure.funMap
      (L := (Grammar.application.sum .predicateModification).language) (D := Ty.Dom D)
      (Grammar.Sym.binary
        (Sum.inl (α := Application l r u) (β := PredicateModification l r u) m)) p =
      Application.eval D m p.1 p.2 :=
  rfl

@[simp] theorem Grammar.funMap_application_sum_predicateModification_inr {D : B → Type}
    {l r u : Ty B} (m : PredicateModification l r u) (p : l.Dom D × r.Dom D) :
    MSFirstOrder.Language.Structure.funMap
      (L := (Grammar.application.sum .predicateModification).language) (D := Ty.Dom D)
      (Grammar.Sym.binary
        (Sum.inr (α := Application l r u) (β := PredicateModification l r u) m)) p =
      PredicateModification.eval D m p.1 p.2 :=
  rfl

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
theorem Grammar.length_binaryRules_application_sum_predicateModification_le_one [DecidableEq B]
    (l r : Ty B) :
    (Grammar.LocallyFinite.binaryRules (G := Grammar.application.sum .predicateModification)
      l r).length ≤ 1 := by
  simp only [Grammar.LocallyFinite.binaryRules, List.length_append, List.length_map]
  rcases l with _ | _ | ⟨a, b⟩ | _ <;> rcases r with _ | _ | ⟨c, d⟩ | _ <;>
    (try rcases b with _ | _ | _ | _) <;> simp <;> split_ifs <;> (try simp) <;>
    first
    | exact Ty.ne_fn_fn_self _ _ _ _ (by assumption) (by assumption)
    | (obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›; exact Ty.ne_fn_self _ _ (by assumption))

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

/-- The grammar of event identification. -/
@[reducible] def Grammar.eventIdentification (x s : Ty B) : Grammar (Ty B) :=
  ⟨fun _ _ ↦ Empty, EventIdentification x s⟩

instance (x s : Ty B) (D : B → Type) :
    (Grammar.eventIdentification x s).language.Structure (Ty.Dom D) :=
  Grammar.structure nofun (EventIdentification.eval D)

/-- A relation of individuals to events is identified with a predicate of events, in either
order. -/
instance [DecidableEq B] (x s : Ty B) : (Grammar.eventIdentification x s).LocallyFinite where
  unaryRules _ := []
  binaryRules l r :=
    (if h : l = (x ⇒ s ⇒ .t) ∧ r = (s ⇒ .t) then
      [⟨x ⇒ s ⇒ .t, by obtain ⟨rfl, rfl⟩ := h; exact .left⟩]
    else []) ++
    if h : l = (s ⇒ .t) ∧ r = (x ⇒ s ⇒ .t) then
      [⟨x ⇒ s ⇒ .t, by obtain ⟨rfl, rfl⟩ := h; exact .right⟩]
    else []
  mem_unaryRules := nofun
  mem_binaryRules m := by cases m <;> simp

end Interpreter
