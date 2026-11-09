module

public import Linglib.Semantics.Composition.Interpreter.Sorts
public import Linglib.Semantics.Composition.Interpreter.Mode
public import Linglib.Semantics.Composition.EventIdentification
public import Linglib.Semantics.Modification.Basic

/-!
# The basic combinators

The basic modes of combination of the library's grammar are functional application in either
order, predicate modification, and Kratzer's event identification. The types of two daughters
select at most one of them, and [every combinator is the one its types
select](##Interpreter.Ty.mode?_eq_some). Predicate modification applies at the sorts the
literature argues for, not at every predicate type.

## Main definitions

* `Interpreter.Combinator`: the basic combinators, typed by the two daughters and the mother.
* `Interpreter.Ty.mode?`, `Interpreter.Ty.combine?`: the combinator two daughters' types select,
  and the type they compose to.
* `Interpreter.Combinator.eval`: the mother's denotation from the daughters'.
* `Interpreter.combinators`: the combinators as the basic modes of an effect-driven grammar.

## References

* [heim-kratzer-1998]
* [kratzer-1996]
* [wellwood-2015]
* [winter-2001b]
-/

@[expose] public section

namespace Interpreter

/-- The sorts whose predicates predicate modification intersects: individuals
([heim-kratzer-1998]), eventualities ([wellwood-2015]), and pluralities, the sets of individuals
of which collective predicates hold ([winter-2001b]). -/
inductive Combinator.PredicateSort : Ty Base → Prop
  /-- Predicates of individuals. -/
  | individual : PredicateSort .e
  /-- Predicates of eventualities. -/
  | eventuality : PredicateSort .v
  /-- Predicates of pluralities. -/
  | plurality : PredicateSort (.e ⇒ .t)

attribute [simp] Combinator.PredicateSort.individual Combinator.PredicateSort.eventuality
  Combinator.PredicateSort.plurality

/-- The basic combinators, typed by the two daughters and the mother: functional application,
predicate modification of two predicates of one sort, and event identification of a role head
with a predicate of eventualities ([kratzer-1996]). All but predicate modification come in both
orders. -/
inductive Combinator : Ty Base → Ty Base → Ty Base → Type where
  /-- Functional application, the left daughter the function. -/
  | functionalLeft {σ τ : Ty Base} : Combinator (σ ⇒ τ) σ τ
  /-- Functional application, the right daughter the function. -/
  | functionalRight {σ τ : Ty Base} : Combinator σ (σ ⇒ τ) τ
  /-- Predicate modification, the intersection of two predicates of a sort it applies to. -/
  | predicateModification {σ : Ty Base} (h : Combinator.PredicateSort σ) :
      Combinator (σ ⇒ .t) (σ ⇒ .t) (σ ⇒ .t)
  /-- Event identification, the role head the left daughter. -/
  | eventIdentificationLeft : Combinator (.e ⇒ .v ⇒ .t) (.v ⇒ .t) (.e ⇒ .v ⇒ .t)
  /-- Event identification, the role head the right daughter. -/
  | eventIdentificationRight : Combinator (.v ⇒ .t) (.e ⇒ .v ⇒ .t) (.e ⇒ .v ⇒ .t)
  deriving DecidableEq

namespace Combinator

/-! ### Selection by the daughters' types -/

/-- Forward functional application applies when the left daughter is a function on the right
one. -/
def functionalLeft? : (σ₁ σ₂ : Ty Base) → Option (Σ τ, Combinator σ₁ σ₂ τ)
  | .fn σ τ, σ₂ => if h : σ = σ₂ then some ⟨τ, h ▸ functionalLeft⟩ else none
  | _, _ => none

/-- Backward functional application applies when the right daughter is a function on the left. -/
def functionalRight? : (σ₁ σ₂ : Ty Base) → Option (Σ τ, Combinator σ₁ σ₂ τ)
  | σ₁, .fn σ τ => if h : σ = σ₁ then some ⟨τ, h ▸ functionalRight⟩ else none
  | _, _ => none

/-- Predicate modification applies to two predicates of individuals, of eventualities, or of
pluralities. -/
def predicateModification? : (σ₁ σ₂ : Ty Base) → Option (Σ τ, Combinator σ₁ σ₂ τ)
  | .fn .e .t, .fn .e .t => some ⟨_, predicateModification .individual⟩
  | .fn .v .t, .fn .v .t => some ⟨_, predicateModification .eventuality⟩
  | .fn (.fn .e .t) .t, .fn (.fn .e .t) .t => some ⟨_, predicateModification .plurality⟩
  | _, _ => none

/-- Event identification applies to a role head and an eventuality predicate, in either order. -/
def eventIdentification? : (σ₁ σ₂ : Ty Base) → Option (Σ τ, Combinator σ₁ σ₂ τ)
  | .fn .e (.fn .v .t), .fn .v .t => some ⟨_, eventIdentificationLeft⟩
  | .fn .v .t, .fn .e (.fn .v .t) => some ⟨_, eventIdentificationRight⟩
  | _, _ => none

end Combinator

/-- The combinator by which a left daughter of type `σ₁` and a right daughter of type `σ₂`
compose: functional application in either order, predicate modification or event identification.
At most one applies, so the order in which they are tried is immaterial. -/
def Ty.mode? (σ₁ σ₂ : Ty Base) : Option (Σ τ, Combinator σ₁ σ₂ τ) :=
  Combinator.functionalLeft? σ₁ σ₂ <|> Combinator.functionalRight? σ₁ σ₂ <|>
    Combinator.predicateModification? σ₁ σ₂ <|> Combinator.eventIdentification? σ₁ σ₂

/-- The type of the mother of a left daughter of type `σ₁` and a right daughter of type `σ₂`. -/
def Ty.combine? (σ₁ σ₂ : Ty Base) : Option (Ty Base) := (σ₁.mode? σ₂).map (·.1)

/-- At most one combinator composes two daughters of given types. -/
instance {σ₁ σ₂ : Ty Base} : Subsingleton (Σ τ, Combinator σ₁ σ₂ τ) := by
  constructor
  rintro ⟨τ, m⟩ ⟨τ', m'⟩
  cases m <;> cases m' <;> rfl

namespace Combinator

@[simp] theorem mode?_fn_left (σ τ : Ty Base) : (σ ⇒ τ).mode? σ = some ⟨τ, functionalLeft⟩ := by
  simp only [Ty.mode?, functionalLeft?, ↓reduceDIte, Option.orElse_eq_orElse, Option.orElse_eq_or,
    Option.some_or]

/-- Forward functional application applies just when the left daughter is a function on the
right one. -/
@[simp] theorem isSome_functionalLeft?_iff {σ₁ σ₂ : Ty Base} :
    (functionalLeft? σ₁ σ₂).isSome ↔ ∃ τ, σ₁ = (σ₂ ⇒ τ) := by
  cases σ₁ with
  | fn σ τ => by_cases h : σ = σ₂ <;> simp [functionalLeft?, h]
  | _ => simp [functionalLeft?]

/-- Backward functional application applies just when the right daughter is a function on the
left one. -/
@[simp] theorem isSome_functionalRight?_iff {σ₁ σ₂ : Ty Base} :
    (functionalRight? σ₁ σ₂).isSome ↔ ∃ τ, σ₂ = (σ₁ ⇒ τ) := by
  cases σ₂ with
  | fn σ τ => by_cases h : σ = σ₁ <;> simp [functionalRight?, h]
  | _ => simp [functionalRight?]

theorem functionalLeft?_self_fn (σ τ : Ty Base) : functionalLeft? σ (σ ⇒ τ) = none := by
  cases σ with
  | fn a b =>
    simp only [functionalLeft?]
    exact dite_eq_right fun h ↦ by cases h
  | _ => rfl

@[simp] theorem mode?_fn_right (σ τ : Ty Base) :
    σ.mode? (σ ⇒ τ) = some ⟨τ, functionalRight⟩ := by
  simp only [Ty.mode?, functionalLeft?_self_fn, functionalRight?, ↓reduceDIte,
    Option.orElse_eq_orElse, Option.orElse_eq_or, Option.none_or, Option.some_or]

@[simp] theorem mode?_predicateModification {σ : Ty Base} (h : PredicateSort σ) :
    (σ ⇒ .t).mode? (σ ⇒ .t) = some ⟨_, predicateModification h⟩ := by
  cases h <;> rfl

end Combinator

/-- Every combinator is the one its daughters' types select. -/
theorem Ty.mode?_eq_some {σ₁ σ₂ : Ty Base} (p : Σ τ, Combinator σ₁ σ₂ τ) :
    σ₁.mode? σ₂ = some p := by
  obtain ⟨τ, m⟩ := p
  cases m with
  | functionalLeft => exact Combinator.mode?_fn_left _ _
  | functionalRight => exact Combinator.mode?_fn_right _ _
  | predicateModification h => cases h <;> rfl
  | eventIdentificationLeft => rfl
  | eventIdentificationRight => rfl

/-- Two types select a combinator just when one composes them. -/
theorem Ty.isSome_mode?_iff {σ₁ σ₂ : Ty Base} :
    (σ₁.mode? σ₂).isSome ↔ Nonempty (Σ τ, Combinator σ₁ σ₂ τ) :=
  ⟨fun h ↦ ⟨(σ₁.mode? σ₂).get h⟩, fun ⟨p⟩ ↦ by rw [Ty.mode?_eq_some p]; rfl⟩

namespace Combinator

/-- The denotation of a combinator: application, the intersection of two predicates, or event
identification. -/
def eval {E W : Type} {S : Sorts} : {σ₁ σ₂ τ : Ty Base} → Combinator σ₁ σ₂ τ →
    σ₁.Domain E W S → σ₂.Domain E W S → τ.Domain E W S
  | _, _, _, functionalLeft, f, a => f a
  | _, _, _, functionalRight, a, f => f a
  | _, _, _, predicateModification _, p, q => Modifier.intersective p q
  | _, _, _, eventIdentificationLeft, f, p => ArgumentStructure.eventIdentification f p
  | _, _, _, eventIdentificationRight, p, f => ArgumentStructure.eventIdentification f p

end Combinator

/-- The combinators as the basic modes of an effect-driven grammar. -/
def combinators : BasicModes Base := ⟨Combinator, fun σ₁ σ₂ ↦ (σ₁.mode? σ₂).toList⟩

end Interpreter
