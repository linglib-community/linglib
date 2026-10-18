module

public import Linglib.Semantics.Composition.Ty
public import Linglib.Semantics.Composition.EventIdentification
public import Linglib.Semantics.Modification.Basic

/-!
# Composition modes

The composition modes of Heim and Kratzer, with the intensional application of von Fintel and
Heim and the event identification of Kratzer, are typed binary operations: a mode of type
`Mode σ₁ σ₂ τ` composes a left daughter of type `σ₁` and a right daughter of type `σ₂` into a
mother of type `τ`. Functional application, intensional application and event identification
come in two orders, the function or role head being the left or the right daughter. The types of
two daughters select the mode they compose by (`Ty.mode?`), the first that applies in the order
functional application, intensional application, predicate modification, event identification.

A mode denotes an operation on the denotation domains (`Mode.eval`): application, application to
the rigid intension of the argument, the intersection of two predicates, and event
identification. Under an applicative effect a mode composes the daughters' computations in their
linear order (`Mode.evalM`), whichever daughter is the function. In any family of values indexed
by the types, `Mode.combine?` composes two values by the mode their types select.

## Main definitions

* `Montague.Mode`: the composition modes as typed binary operations.
* `Montague.Ty.mode?`, `Montague.Ty.combine?`: the mode two daughters' types select, and the type
  they compose to.
* `Montague.Mode.eval`, `Montague.Mode.evalM`: the denotation of a mode, pure and under an
  applicative effect.
* `Montague.Mode.combine?`: composition by the selected mode in a family of values.

## Main results

* `Montague.Mode.combine?_map`: composing commutes with every map of families that commutes with
  the modes.
* `Montague.Mode.combine?_map_fst`: the type of a composed value is `Ty.combine?` of the
  daughters' types.

## References

* [heim-kratzer-1998]
* [von-fintel-heim-2011]
* [kratzer-1996]
-/

@[expose] public section

namespace Montague

/-- The composition modes are the typed binary operations of functional application, with the
function as either daughter, of intensional application, which applies a daughter expecting an
intension to the rigid intension of its sister in either order ([von-fintel-heim-2011]), of
predicate modification, and of event identification of a role head and an eventuality predicate
in either order ([kratzer-1996]). -/
inductive Mode : Ty → Ty → Ty → Type where
  | functionalLeft {σ τ : Ty} : Mode (σ ⇒ τ) σ τ
  | functionalRight {σ τ : Ty} : Mode σ (σ ⇒ τ) τ
  | intensionalLeft {σ τ : Ty} : Mode (.intens σ ⇒ τ) σ τ
  | intensionalRight {σ τ : Ty} : Mode σ (.intens σ ⇒ τ) τ
  | predicateModification : Mode (.e ⇒ .t) (.e ⇒ .t) (.e ⇒ .t)
  | eventIdentificationLeft : Mode (.e ⇒ .e ⇒ .t) (.e ⇒ .t) (.e ⇒ .e ⇒ .t)
  | eventIdentificationRight : Mode (.e ⇒ .t) (.e ⇒ .e ⇒ .t) (.e ⇒ .e ⇒ .t)
  deriving DecidableEq

namespace Mode

/-! ### Selection by the daughters' types -/

/-- Forward functional application applies when the left daughter is a function on the right one. -/
def functionalLeft? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | .fn σ τ, σ₂ => if h : σ = σ₂ then some ⟨τ, h ▸ functionalLeft⟩ else none
  | _, _ => none

/-- Backward functional application applies when the right daughter is a function on the left one.
 -/
def functionalRight? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | σ₁, .fn σ τ => if h : σ = σ₁ then some ⟨τ, h ▸ functionalRight⟩ else none
  | _, _ => none

/-- Intensional application applies when the left daughter expects the intension of the right one.
 -/
def intensionalLeft? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | .fn (.intens σ) τ, σ₂ => if h : σ = σ₂ then some ⟨τ, h ▸ intensionalLeft⟩ else none
  | _, _ => none

/-- Intensional application applies when the right daughter expects the intension of the left one.
 -/
def intensionalRight? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | σ₁, .fn (.intens σ) τ => if h : σ = σ₁ then some ⟨τ, h ▸ intensionalRight⟩ else none
  | _, _ => none

/-- Predicate modification applies to two predicates. -/
def predicateModification? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | .fn .e .t, .fn .e .t => some ⟨_, predicateModification⟩
  | _, _ => none

/-- Event identification applies to a role head and an eventuality predicate, in either order. -/
def eventIdentification? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | .fn .e (.fn .e .t), .fn .e .t => some ⟨_, eventIdentificationLeft⟩
  | .fn .e .t, .fn .e (.fn .e .t) => some ⟨_, eventIdentificationRight⟩
  | _, _ => none

end Mode

/-- `σ₁.mode? σ₂` is the mode by which a left daughter of type `σ₁` and a right daughter of type
`σ₂` compose, the first that applies of functional application (the left daughter as the
function first), intensional application, predicate modification and event identification, and
`none` when none does. -/
def Ty.mode? (σ₁ σ₂ : Ty) : Option (Σ τ, Mode σ₁ σ₂ τ) :=
  Mode.functionalLeft? σ₁ σ₂ <|> Mode.functionalRight? σ₁ σ₂ <|> Mode.intensionalLeft? σ₁ σ₂ <|>
    Mode.intensionalRight? σ₁ σ₂ <|> Mode.predicateModification? σ₁ σ₂ <|>
      Mode.eventIdentification? σ₁ σ₂

/-- `σ₁.combine? σ₂` is the type a left daughter of type `σ₁` and a right daughter of type `σ₂`
compose to, the mother's type under the mode their types select. -/
def Ty.combine? (σ₁ σ₂ : Ty) : Option Ty := (σ₁.mode? σ₂).map (·.1)

namespace Mode

/-- A function type applies to an argument of its domain, the function on the left. -/
@[simp] theorem mode?_fn_left (σ τ : Ty) : (σ ⇒ τ).mode? σ = some ⟨τ, functionalLeft⟩ := by
  simp only [Ty.mode?, functionalLeft?, ↓reduceDIte, Option.orElse_eq_orElse, Option.orElse_eq_or,
    Option.some_or]

/-- No type is its own argument type, so a type never applies to a function type from itself. -/
theorem functionalLeft?_self_fn (σ τ : Ty) : functionalLeft? σ (σ ⇒ τ) = none := by
  cases σ with
  | fn a b =>
    simp only [functionalLeft?]
    split_ifs with h
    · have := congrArg sizeOf h
      simp only [Ty.fn.sizeOf_spec] at this
      omega
    · rfl
  | _ => rfl

/-- A function type applies to an argument of its domain, the function on the right. -/
@[simp] theorem mode?_fn_right (σ τ : Ty) : σ.mode? (σ ⇒ τ) = some ⟨τ, functionalRight⟩ := by
  simp only [Ty.mode?, functionalLeft?_self_fn, functionalRight?, ↓reduceDIte,
    Option.orElse_eq_orElse, Option.orElse_eq_or, Option.none_or, Option.some_or]

/-- Two predicates compose by predicate modification. -/
@[simp] theorem mode?_predicateModification :
    (Ty.e ⇒ .t).mode? (.e ⇒ .t) = some ⟨_, predicateModification⟩ := by
  simp [Ty.mode?, functionalLeft?, functionalRight?, intensionalLeft?, intensionalRight?,
    predicateModification?]

/-! ### Denotation -/

variable {E W D : Type} {σ₁ σ₂ τ : Ty}

/-- A mode denotes application, application to the rigid intension of the argument, the
intersection of two predicates, or event identification. -/
@[simp] def eval : Mode σ₁ σ₂ τ → Ty.Domain E W σ₁ D → Ty.Domain E W σ₂ D → Ty.Domain E W τ D
  | functionalLeft, f, a => f a
  | functionalRight, a, f => f a
  | intensionalLeft, f, a => f fun _ ↦ a
  | intensionalRight, a, f => f fun _ ↦ a
  | predicateModification, p, q => Modifier.intersective p q
  | eventIdentificationLeft, f, p => ArgumentStructure.eventIdentification f p
  | eventIdentificationRight, p, f => ArgumentStructure.eventIdentification f p

/-- The denotation of a mode under an applicative effect, which runs the left daughter's
computation first. -/
def evalM {M : Type → Type} [Applicative M] (m : Mode σ₁ σ₂ τ) (a : M (Ty.Domain E W σ₁ D))
    (b : M (Ty.Domain E W σ₂ D)) : M (Ty.Domain E W τ D) :=
  m.eval <$> a <*> b

/-- At the identity effect a mode denotes its pure denotation. -/
@[simp] theorem evalM_id (m : Mode σ₁ σ₂ τ) (a : Ty.Domain E W σ₁ D) (b : Ty.Domain E W σ₂ D) :
    m.evalM (M := Id) a b = m.eval a b := rfl

/-! ### Composition in a family of values -/

variable {V V' : Ty → Type*}

/-- Two values compose by the mode their types select, interpreted by `op`, and not at all when
no mode applies. -/
def combine? (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ) (d₁ d₂ : Σ ty, V ty) :
    Option (Σ ty, V ty) :=
  (d₁.1.mode? d₂.1).map fun p ↦ ⟨p.1, op p.2 d₁.2 d₂.2⟩

/-- The type of a composed value is the type the mode selects, a function of the daughters' types
alone. -/
@[simp] theorem combine?_map_fst (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ)
    (d₁ d₂ : Σ ty, V ty) : (combine? op d₁ d₂).map (·.1) = d₁.1.combine? d₂.1 := by
  simp [combine?, Ty.combine?, Option.map_map, Function.comp_def]

/-- Composing commutes with every map of families that commutes with the modes. -/
theorem combine?_map {op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ}
    {op' : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V' σ₁ → V' σ₂ → V' τ} {h : ∀ {ty : Ty}, V ty → V' ty}
    (hh : ∀ {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) a b, h (op m a b) = op' m (h a) (h b))
    (d₁ d₂ : Σ ty, V ty) :
    (combine? op d₁ d₂).map (fun d ↦ ⟨d.1, h d.2⟩) =
      combine? op' ⟨d₁.1, h d₁.2⟩ ⟨d₂.1, h d₂.2⟩ := by
  simp [combine?, Option.map_map, Function.comp_def, hh]

@[simp] theorem combine?_fn_left (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ)
    {σ τ : Ty} (f : V (σ ⇒ τ)) (a : V σ) :
    combine? op ⟨σ ⇒ τ, f⟩ ⟨σ, a⟩ = some ⟨τ, op functionalLeft f a⟩ := by
  simp [combine?]

@[simp] theorem combine?_fn_right (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ)
    {σ τ : Ty} (a : V σ) (f : V (σ ⇒ τ)) :
    combine? op ⟨σ, a⟩ ⟨σ ⇒ τ, f⟩ = some ⟨τ, op functionalRight a f⟩ := by
  simp [combine?]

@[simp] theorem combine?_predicateModification
    (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ) (p q : V (.e ⇒ .t)) :
    combine? op ⟨.e ⇒ .t, p⟩ ⟨.e ⇒ .t, q⟩ = some ⟨.e ⇒ .t, op predicateModification p q⟩ := by
  simp [combine?]

end Mode

end Montague
