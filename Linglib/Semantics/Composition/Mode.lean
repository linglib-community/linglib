module

public import Linglib.Semantics.Composition.Ty
public import Linglib.Semantics.Composition.EventIdentification
public import Linglib.Semantics.Modification.Basic

/-!
# Composition modes

A *composition mode* of type `Mode σ₁ σ₂ τ` composes a left daughter of type `σ₁` and a right
daughter of type `σ₂` into a mother of type `τ`. The modes are Heim and Kratzer's, with the
intensional application of von Fintel and Heim and the event identification of Kratzer;
functional application, intensional application and event identification come in both orders.
The daughters' types select the mode (`Ty.mode?`): the first that applies among functional
application, intensional application, predicate modification and event identification.

A mode denotes an operation on the denotation domains (`Mode.eval`). Under an applicative effect a
mode composes the daughters' computations in linear order, whichever daughter is the function
(`Mode.evalM`). In any family of values indexed by types, `Mode.combine?` composes two values by
the mode their types select.

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

/-- The composition modes, typed by the two daughters and the mother: functional application;
intensional application of a daughter expecting an intension to the rigid intension of its sister
([von-fintel-heim-2011]); predicate modification of two predicates of one sort; and event
identification of a role head with a predicate of eventualities, Kratzer's (23) ([kratzer-1996]).
All but predicate modification come in both orders. -/
inductive Mode : Ty → Ty → Ty → Type where
  /-- Functional application, the left daughter the function. -/
  | functionalLeft {σ τ : Ty} : Mode (σ ⇒ τ) σ τ
  /-- Functional application, the right daughter the function. -/
  | functionalRight {σ τ : Ty} : Mode σ (σ ⇒ τ) τ
  /-- Intensional application, the left daughter taking the intension of the right. -/
  | intensionalLeft {σ τ : Ty} : Mode (.intens σ ⇒ τ) σ τ
  /-- Intensional application, the right daughter taking the intension of the left. -/
  | intensionalRight {σ τ : Ty} : Mode σ (.intens σ ⇒ τ) τ
  /-- Predicate modification, the intersection of two predicates of a sort. -/
  | predicateModification {σ : Ty} : Mode (σ ⇒ .t) (σ ⇒ .t) (σ ⇒ .t)
  /-- Event identification, the role head the left daughter. -/
  | eventIdentificationLeft : Mode (.e ⇒ .v ⇒ .t) (.v ⇒ .t) (.e ⇒ .v ⇒ .t)
  /-- Event identification, the role head the right daughter. -/
  | eventIdentificationRight : Mode (.v ⇒ .t) (.e ⇒ .v ⇒ .t) (.e ⇒ .v ⇒ .t)
  deriving DecidableEq

namespace Mode

/-! ### Selection by the daughters' types -/

/-- Forward functional application applies when the left daughter is a function on the right one. -/
def functionalLeft? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | .fn σ τ, σ₂ => if h : σ = σ₂ then some ⟨τ, h ▸ functionalLeft⟩ else none
  | _, _ => none

/-- Backward functional application applies when the right daughter is a function on the left. -/
def functionalRight? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | σ₁, .fn σ τ => if h : σ = σ₁ then some ⟨τ, h ▸ functionalRight⟩ else none
  | _, _ => none

/-- Intensional application applies when the left daughter expects the right one's intension. -/
def intensionalLeft? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | .fn (.intens σ) τ, σ₂ => if h : σ = σ₂ then some ⟨τ, h ▸ intensionalLeft⟩ else none
  | _, _ => none

/-- Intensional application applies when the right daughter expects the left one's intension. -/
def intensionalRight? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | σ₁, .fn (.intens σ) τ => if h : σ = σ₁ then some ⟨τ, h ▸ intensionalRight⟩ else none
  | _, _ => none

/-- Predicate modification applies to two predicates of individuals or two predicates of
eventualities ([wellwood-2015]). -/
def predicateModification? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | .fn .e .t, .fn .e .t => some ⟨_, predicateModification⟩
  | .fn .v .t, .fn .v .t => some ⟨_, predicateModification⟩
  | _, _ => none

/-- Event identification applies to a role head and an eventuality predicate, in either order. -/
def eventIdentification? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | .fn .e (.fn .v .t), .fn .v .t => some ⟨_, eventIdentificationLeft⟩
  | .fn .v .t, .fn .e (.fn .v .t) => some ⟨_, eventIdentificationRight⟩
  | _, _ => none

end Mode

/-- The mode by which a left daughter of type `σ₁` and a right daughter of type `σ₂` compose: the
first that applies of functional application (with the left daughter as the function first),
intensional application, predicate modification and event identification. -/
def Ty.mode? (σ₁ σ₂ : Ty) : Option (Σ τ, Mode σ₁ σ₂ τ) :=
  Mode.functionalLeft? σ₁ σ₂ <|> Mode.functionalRight? σ₁ σ₂ <|> Mode.intensionalLeft? σ₁ σ₂ <|>
    Mode.intensionalRight? σ₁ σ₂ <|> Mode.predicateModification? σ₁ σ₂ <|>
      Mode.eventIdentification? σ₁ σ₂

/-- The type of the mother of a left daughter of type `σ₁` and a right daughter of type `σ₂`,
under the mode their types select. -/
def Ty.combine? (σ₁ σ₂ : Ty) : Option Ty := (σ₁.mode? σ₂).map (·.1)

namespace Mode

@[simp] theorem mode?_fn_left (σ τ : Ty) : (σ ⇒ τ).mode? σ = some ⟨τ, functionalLeft⟩ := by
  simp only [Ty.mode?, functionalLeft?, ↓reduceDIte, Option.orElse_eq_orElse, Option.orElse_eq_or,
    Option.some_or]

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

@[simp] theorem mode?_fn_right (σ τ : Ty) : σ.mode? (σ ⇒ τ) = some ⟨τ, functionalRight⟩ := by
  simp only [Ty.mode?, functionalLeft?_self_fn, functionalRight?, ↓reduceDIte,
    Option.orElse_eq_orElse, Option.orElse_eq_or, Option.none_or, Option.some_or]

@[simp] theorem mode?_predicateModification :
    (Ty.e ⇒ .t).mode? (.e ⇒ .t) = some ⟨_, predicateModification⟩ := by
  simp [Ty.mode?, functionalLeft?, functionalRight?, intensionalLeft?, intensionalRight?,
    predicateModification?]

/-! ### Denotation -/

variable {E W : Type} {S : Sorts} {σ₁ σ₂ τ : Ty}

/-- The denotation of a mode: application, application to the rigid intension of the argument,
intersection of two predicates, or event identification. -/
@[simp] def eval : Mode σ₁ σ₂ τ → Ty.Domain E W σ₁ S → Ty.Domain E W σ₂ S → Ty.Domain E W τ S
  | functionalLeft, f, a => f a
  | functionalRight, a, f => f a
  | intensionalLeft, f, a => f fun _ ↦ a
  | intensionalRight, a, f => f fun _ ↦ a
  | predicateModification, p, q => Modifier.intersective p q
  | eventIdentificationLeft, f, p => ArgumentStructure.eventIdentification f p
  | eventIdentificationRight, p, f => ArgumentStructure.eventIdentification f p

/-- The denotation of a mode under an applicative effect, which runs the left daughter's
computation first. -/
def evalM {M : Type → Type} [Applicative M] (m : Mode σ₁ σ₂ τ) (a : M (Ty.Domain E W σ₁ S))
    (b : M (Ty.Domain E W σ₂ S)) : M (Ty.Domain E W τ S) :=
  m.eval <$> a <*> b

@[simp] theorem evalM_id (m : Mode σ₁ σ₂ τ) (a : Ty.Domain E W σ₁ S) (b : Ty.Domain E W σ₂ S) :
    m.evalM (M := Id) a b = m.eval a b := rfl

/-! ### Composition in a family of values -/

variable {V V' : Ty → Type*}

/-- Two values compose by the mode their types select, interpreted by `op`, and not at all when
no mode applies. -/
def combine? (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ) (d₁ d₂ : Σ ty, V ty) :
    Option (Σ ty, V ty) :=
  (d₁.1.mode? d₂.1).map fun p ↦ ⟨p.1, op p.2 d₁.2 d₂.2⟩

/-- The type of a composed value depends only on the daughters' types. -/
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

@[simp] theorem combine?_predicateModification_v
    (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ) (p q : V (.v ⇒ .t)) :
    combine? op ⟨.v ⇒ .t, p⟩ ⟨.v ⇒ .t, q⟩ = some ⟨.v ⇒ .t, op predicateModification p q⟩ := by
  simp [combine?, Ty.mode?, functionalLeft?, functionalRight?, intensionalLeft?,
    intensionalRight?, predicateModification?]

end Mode

end Montague
